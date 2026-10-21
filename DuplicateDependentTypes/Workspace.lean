import Lean
import Lake
import Lake.Load.Workspace

/-!
# The Lake workspace

`lake exe` runs the tool with the workspace's `LEAN_PATH`, so every built module of the
workspace and its dependencies is on the search path. The workspace's own modules are those of
the root package's `lean_lib`s: their roots and every source file below them (Lake's configuration
loader, without resolving dependencies). A module's source file is found from its library's
`srcDir`, or else from its `.olean`: `<pkg>/.lake/build/lib/lean/A/B.olean` ↦ `<pkg>/A/B.lean`,
`<sysroot>/lib/lean/A/B.olean` ↦ `<sysroot>/src/lean/A/B.lean`.
-/

namespace DuplicateDependentTypes

open Lean System

structure Workspace where
  dir : FilePath
  name : String
  /-- The modules of the root package's libraries, with their source files. -/
  modules : Array (Name × FilePath)

/-- `dir` or its nearest ancestor with a lakefile. -/
partial def findWorkspaceDir (dir : FilePath) : IO (Option FilePath) := do
  if (← (dir / "lakefile.toml").pathExists) || (← (dir / "lakefile.lean").pathExists) then
    return some dir
  match dir.parent with
  | some p => if p == dir then return none else findWorkspaceDir p
  | none => return none

private def modDir (base : FilePath) : Name → FilePath
  | .str p h => modDir base p / h
  | _ => base

def loadWorkspace (dir : FilePath) : IO Workspace := do
  let (elan?, lean?, lake?) ← Lake.findInstall?
  let some lean := lean? | throw <| IO.userError "no Lean installation found"
  let lakeEnv ← (Lake.Env.compute (lake?.getD (.ofLean lean)) lean elan?).toIO
    fun e => IO.userError s!"could not compute the Lake environment: {e}"
  let some ws ← (Lake.loadWorkspaceRoot { lakeEnv, wsDir := dir }).toBaseIO
    | throw <| IO.userError s!"Lake could not load the package configuration in {dir}"
  let mods ← IO.mkRef (#[] : Array (Name × FilePath))
  for lib in ws.root.leanLibs do
    for root in lib.roots do
      let f := modToFilePath lib.srcDir root "lean"
      if ← f.pathExists then mods.modify (·.push (root, f))
      let sub := modDir lib.srcDir root
      if ← sub.isDir then
        forEachModuleInDir sub fun m => mods.modify (·.push (root ++ m, modToFilePath lib.srcDir (root ++ m) "lean"))
  let sorted := (← mods.get).qsort (·.1.toString < ·.1.toString)
  let modules := sorted.foldl (fun acc m => if acc.back?.map (·.1) == some m.1 then acc else acc.push m) #[]
  return { dir, name := ws.root.prettyName, modules }

private partial def oleansIn (dir : FilePath) (pre : Name) (acc : Array Name) : IO (Array Name) := do
  let mut acc := acc
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      acc ← oleansIn entry.path (pre ++ .mkSimple entry.fileName) acc
    else if entry.path.extension == some "olean" then
      acc := acc.push (pre ++ .mkSimple (entry.path.fileStem.getD ""))
  return acc

/-- The modules to import for a prefix: its own `.olean` if there is one, otherwise every module
below it on the search path, sorted (the order fixes the extraction order). -/
def modulesFor (p : Name) : IO (Array Name) := do
  let sp ← searchPathRef.get
  for dir in sp do
    if ← (modToFilePath dir p "olean").pathExists then return #[p]
  let mut out := #[]
  for dir in sp do
    let sub := modDir dir p
    if ← sub.isDir then out ← oleansIn sub p out
  return out.qsort Name.lt

def oleanOf? (m : Name) : IO (Option FilePath) := do
  match ← (findOLean m).toBaseIO with
  | .ok p => return if ← p.pathExists then some p else none
  | .error _ => return none

/-- The package directory of a module's `.olean` (`<pkg>/.lake/build/lib/lean/A/B.olean`) or of
Lean's own (`<sysroot>/lib/lean/A/B.olean`), and the source directory there. -/
def packageOf? (m : Name) : IO (Option (FilePath × FilePath)) := do
  let some p ← oleanOf? m | return none
  for (marker, src) in [("/.lake/build/lib/lean/", "/"), ("/lib/lean/", "/src/lean/")] do
    if let [pkg, _] := p.toString.splitOn marker then return some (pkg, pkg ++ src)
  return none

/-- The source file of a module that is not one of the workspace's own. -/
def sourceOfOLean (m : Name) : IO (Option FilePath) := do
  let some (_, src) ← packageOf? m | return none
  let f := modToFilePath src m "lean"
  return if ← f.pathExists then some f else none

def gitRev? (dir : FilePath) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := "git", args := #["-C", dir.toString, "rev-parse", "HEAD"] }
    return if out.exitCode == 0 then some out.stdout.trimAscii.toString else none
  catch _ => return none

/-- Name, revision and URL of the packages in the workspace's `lake-manifest.json` and of the
workspace itself that own one of the modules `mods`. -/
def versions (ws : Workspace) (mods : Array Name) : IO (Array Json) := do
  let realPath (d : FilePath) : IO String := do
    try return (← IO.FS.realPath d).toString catch _ => return d.toString
  let mut owners : Std.HashSet String := {}
  for m in mods do
    if let some (pkg, _) ← packageOf? m then owners := owners.insert (← realPath pkg)
  let mut out := #[]
  if let some j := (Json.parse (← IO.FS.readFile (ws.dir / "lake-manifest.json"))).toOption then
    let pkgsDir := (j.getObjValAs? String "packagesDir").toOption.getD ".lake/packages"
    for p in (j.getObjValAs? (Array Json) "packages").toOption.getD #[] do
      let (.ok name, .ok rev) := (p.getObjValAs? String "name", p.getObjValAs? String "rev") | continue
      let sub := (p.getObjValAs? String "subDir").toOption.getD ""
      if owners.contains (← realPath (ws.dir / pkgsDir / name / sub)) then
        out := out.push (Json.mkObj [("name", name), ("rev", rev), ("url", (p.getObjValAs? String "url").toOption.getD "")])
  if owners.contains (← realPath ws.dir) then
    if let some rev ← gitRev? ws.dir then out := out.push (Json.mkObj [("name", ws.name), ("rev", rev)])
  return out

end DuplicateDependentTypes
