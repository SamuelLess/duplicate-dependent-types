# duplicate-dependent-types

Finds the theorems of a Lean project whose statements are the same type up to isomorphism —
reordered or curried hypotheses, `∃`/`∧` currying, swapped sides of `=`/`↔`/`∨`, `¬`/`≠` unfolded
— and that are each proved separately. Statements are normalised by taking them apart into a
graph of hypotheses and conclusions, then compared up to renaming and reordering. The result is a
JSONL file with one line per group of duplicates and a self-contained HTML page to browse them.

## Installation

Lean core only, no other dependencies. In `lakefile.toml`:

```toml
[[require]]
name = "duplicate-dependent-types"
git = "https://github.com/SamuelLess/duplicate-dependent-types"
rev = "main"
```

or in `lakefile.lean`:

```lean
require «duplicate-dependent-types» from git "https://github.com/SamuelLess/duplicate-dependent-types" @ "main"
```

then `lake update duplicate-dependent-types`.

## Usage

```
lake build                                  # the tool reads your project's .olean files
lake exe duplicates                         # your libraries → duplicates.jsonl, duplicates.html
lake exe duplicates --modules A.B,C         # only the modules below these prefixes
lake exe duplicates --jsonl out.jsonl       # only the JSONL, to this file
lake exe duplicates --html out.html         # only the HTML, to this file
lake exe duplicates --jobs 8                # parallel tasks (default 4)
```

The HTML page is one file (data, styles and script inlined) with a filterable list of the groups
and a view of each group's statements and sources; it can be uploaded as a CI artifact.

## Output

One JSON object per line and group:

| field | |
|---|---|
| `id`, `r` | group id; rank (statements equal only up to isomorphism first) |
| `a`, `b`, `n`, `m` | the first two independent proofs; number of members; their modules |
| `sk` | how the statements compare: `same` (syntactically), `defeq`, `not defeq` (only up to isomorphism) |
| `loc` | `same file`, `cross-file`, `cross-area` (another directory), `cross-package` |
| `pk` | packages (`core` = `Init`, `Std`, `Lean`, `Lake`; otherwise the root module) |
| `tr` | `all trivial`, `some trivial`, `substantive` (proof term ≤ 128 objects and proof text ≤ 110 characters) |
| `u` | `all used`, `one side unused`, `none used` (by constants outside the group) |
| `tw` | why `a`, `b` look like an API pair written on purpose (`adjacent`, `orientation`, `primed`, `contains-mem`, `symmetric names`, `simp`, `internal`), or `""` |
| `members` | `name`, `module`, `file`, `line`, `end`, `sig` (the signature), `src` (the source from line `from`), `dep` (why it is not an independent proof: it uses another member, is deprecated or generated with one), `gen`, `rel`, `trivial`, `used` |

## Caveats

* **Build first.** The tool reads `.olean` files; modules without one are skipped.
* **Theorems only.** Definitions, instances and private or auto-generated declarations are not
  compared, and very large statements are skipped.
* **Usage** counts the constants in the imported environment only: with `--modules`, users in
  other modules are not seen.
* **Memory and time.** All of Mathlib (240,000 theorems) takes about 2 minutes and 9.5 GB with
  `--jobs 6`; 2,650 of its modules take one minute and 6 GB. Restrict with `--modules` on small
  machines.
