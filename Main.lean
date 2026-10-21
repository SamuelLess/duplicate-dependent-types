import DuplicateDependentTypes

open Lean System DuplicateDependentTypes

def usage : String :=
  "usage: lake exe duplicates [--modules A.B,C] [--jsonl FILE] [--html FILE] [--jobs N]

Finds the theorems of a Lake project whose statements are the same type up to isomorphism.
Analyses the workspace's own libraries (build them first), or the modules below the given
prefixes. Writes duplicates.jsonl and duplicates.html, or only the outputs given."

structure Args where
  modules : Array Name := #[]
  jsonl? : Option FilePath := none
  html? : Option FilePath := none
  jobs : Nat := 4

partial def parseArgs : List String → Args → Except String Args
  | [], o => pure o
  | "--modules" :: v :: rest, o =>
    parseArgs rest { o with modules := o.modules ++ ((v.splitOn ",").filter (!·.isEmpty)).toArray.map (·.toName) }
  | "--jsonl" :: v :: rest, o => parseArgs rest { o with jsonl? := some v }
  | "--html" :: v :: rest, o => parseArgs rest { o with html? := some v }
  | "--jobs" :: v :: rest, o => match v.toNat? with
    | some n => parseArgs rest { o with jobs := max 1 n }
    | none => throw s!"--jobs expects a number, got '{v}'"
  | a :: _, _ => throw s!"unknown or incomplete argument '{a}'\n\n{usage}"

def coreContext : Core.Context :=
  { fileName := "<duplicates>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 10000 }

/-- The modules to import and the prefixes to analyse. -/
def selectModules (o : Args) (ws? : Option Workspace) : IO (Array Name × Array Name) := do
  if o.modules.isEmpty then
    let some ws := ws? | throw <| IO.userError "not inside a Lake workspace; pass --modules"
    let built ← ws.modules.filterM fun (m, _) => return (← oleanOf? m).isSome
    if built.size < ws.modules.size then
      IO.eprintln s!"duplicates: {ws.modules.size - built.size} module(s) without .olean skipped (run `lake build` first)"
    let mods := built.map (·.1)
    return (mods, mods)
  let mut imports := #[]
  for p in o.modules do
    let ms ← modulesFor p
    if ms.isEmpty then throw <| IO.userError s!"no built module {p} on the search path"
    imports := imports ++ ms
  return (imports, o.modules)

unsafe def main (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println usage; return 0
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 1
  let (jsonl?, html?) := if o.jsonl?.isNone && o.html?.isNone
    then (some ("duplicates.jsonl" : FilePath), some ("duplicates.html" : FilePath)) else (o.jsonl?, o.html?)
  let t0 ← IO.monoMsNow
  -- Lake's DSL elaborators, to read a `lakefile.lean`
  enableInitializersExecution
  let cwd ← IO.currentDir
  let ws? ← (← findWorkspaceDir cwd).mapM loadWorkspace
  -- Lake's loader sets the search path to its own; `lake exe` set ours in `LEAN_PATH`
  initSearchPath (← findSysroot)
  let (imports, prefixes) ← selectModules o ws?
  IO.eprintln s!"duplicates: importing {imports.size} module(s)"
  enableInitializersExecution  -- again: loading a `lakefile.lean` resets it
  let env ← importModules (imports.map ({ module := · })) {} (trustLevel := 1024) (leakEnv := true) (loadExts := true)
  let run {α} (x : MetaM α) : IO α := return (← x.toIO coreContext { env }).1
  let c ← run (cluster prefixes o.jobs)
  let mut files : Std.HashMap Name FilePath := ws?.elim {} (·.modules.foldl (fun m (n, f) => m.insert n f) {})
  for d in c.classes.flatten do
    unless files.contains d.module do
      if let some f ← sourceOfOLean d.module then files := files.insert d.module f
  let fileOf := fun m => files[m]?.map fun f => (if f.isAbsolute then f else cwd / f).normalize
  let cs ← checkouts ws?
  let mut urls : Std.HashMap Name String := {}
  for d in c.classes.flatten do
    if let some f := fileOf d.module then
      if let some u ← sourceUrl? cs f then urls := urls.insert d.module u
  let annotated ← run do
    let parts ← spawnAll ((shares c.classes.size o.jobs 1).map fun idxs =>
      idxs.mapM fun i => return (i, ← annotateClass fileOf c.classes[i]!))
    let groups := (parts.flatten.qsort (·.1 < ·.1)).map (·.2)
    markUsed (dropMirrors (groups.filter fun ms => (ms.filter (·.dep?.isNone)).size ≥ 2)) o.jobs
  -- rank: groups with statements equal only up to isomorphism first, then more independent proofs
  let strength (ms : Array Member) : Nat :=
    10000 * ms.foldl (fun s m => max s (match m.rel? with | some "not defeq" => 2 | some "defeq" => 1 | _ => 0)) 0 +
      (ms.filter (·.dep?.isNone)).size
  let ranked := (annotated.mapIdx (·, ·)).qsort fun (i, x) (j, y) =>
    strength x > strength y || (strength x == strength y && i < j)
  let wsDir := (ws?.map (·.dir)).getD cwd
  let lines := ranked.mapIdx fun r (i, ms) => (groupJson i (r + 1) wsDir (urls[·]?) ms).compress
  if let some p := jsonl? then
    IO.FS.writeFile p ("".intercalate (lines.toList.map (· ++ "\n")))
  if let some p := html? then
    let project := if o.modules.isEmpty then (ws?.map (·.name)).getD "" else ", ".intercalate (o.modules.toList.map toString)
    let info := Json.mkObj [("project", project), ("lean", Lean.versionString),
      ("versions", toJson (← versions cs (env.header.moduleNames.filter (isBelow prefixes)))), ("root", wsDir.toString)]
    IO.FS.writeFile p (html info lines)
  IO.println s!"duplicates: {c.analysed} of {c.extracted} theorems analysed, {lines.size} groups of duplicates, {(← IO.monoMsNow) - t0} ms"
  for p in [jsonl?, html?].filterMap id do IO.println s!"duplicates: wrote {p}"
  return 0
