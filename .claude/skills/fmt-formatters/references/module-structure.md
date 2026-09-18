# Formatter Module Structure

## Directory layout

`src/Lean/Fmt/Formatters/` mirrors the structure of the modules that contain the
syntax/parsers being formatted:

| Parsers defined in | Formatters live in |
|---|---|
| `Init.Notation` (`src/Init/Notation.lean`) | `src/Lean/Fmt/Formatters/Init/Notation.lean` |
| `Std.Tactic.Do.Syntax` (`src/Std/Tactic/Do/Syntax.lean`) | `src/Lean/Fmt/Formatters/Std/Tactic/Do/Syntax.lean` |
| `Lean.Parser.Command` (`src/Lean/Parser/Command.lean`) | `src/Lean/Fmt/Formatters/Lean/Parser/Command.lean` |
| `Lean.Parser.Term.Basic` | `src/Lean/Fmt/Formatters/Lean/Parser/Term/Basic.lean` |
| `Lean.Meta.Tactic.Grind.Parser` | `src/Lean/Fmt/Formatters/Lean/Meta/Tactic/Grind/Parser.lean` |

There are three top-level trees, one per source tree that declares syntax: `Init/`, `Std/`,
and `Lean/`. The formatters for Lake's syntax are in a separate tree (see
[Lake formatters](#lake-formatters)).

Formatter modules are registered in aggregation files that mirror the hierarchy:

- `src/Lean/Fmt/Formatters.lean` publicly imports `Lean.Fmt.Formatters.Init`,
  `Lean.Fmt.Formatters.Std` and `Lean.Fmt.Formatters.Lean`
- `src/Lean/Fmt/Formatters/Init.lean` publicly imports each
  `Lean.Fmt.Formatters.Init.*` module (e.g. `...Init.Notation`, `...Init.Tactics`)
- `src/Lean/Fmt/Formatters/Std.lean` publicly imports `...Std.Data`, `...Std.Do`,
  `...Std.Internal`, `...Std.Sat`, `...Std.Tactic`, `...Std.Time` and `...Std.WP`
- `src/Lean/Fmt/Formatters/Lean.lean` publicly imports each `Lean.Fmt.Formatters.Lean.*`
  module (`...Lean.Data`, `...Lean.Elab`, `...Lean.Meta`, `...Lean.Parser`, `...Lean.Server`, …)
- `src/Lean/Fmt/Formatters/Lean/Parser.lean` publicly imports each
  `Lean.Fmt.Formatters.Lean.Parser.*` module
- `src/Lean/Fmt/Formatters/Lean/Meta.lean` → `...Meta.Tactic` → `...Tactic.Grind` → etc.

An aggregation file that would import nothing must not exist. When a change removes the last
formatter of a subtree, delete the now-empty module and its `public import` line as well.

**When adding a new formatter module, add a `public import` for it to the appropriate
aggregation file** (creating intermediate aggregation files if the path is new),
otherwise the formatters are never registered.

## Module header

New formatter modules use this header (get the year with `date +%Y`; author per repo
conventions):

```lean
/-
Copyright (c) <year> Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import <module of parser that formatters are for>
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

<formatters>
```

Notes:

- The `meta import` of the parser module is what makes the quotation patterns
  (`` `(Parser.Command.export| ...) ``) work — import the module that *defines* the
  parsers being formatted (e.g. `meta import Lean.Parser.Command`).
- These are `prelude` modules: nothing is auto-imported. Add `import Init.*` modules
  for stdlib features as needed (e.g. `import Init.While` for `while`/`repeat`,
  `import Init.Data` for common data structures).
- `import Lean.Fmt.FmtM.CommonFormatters` for the shared `fmt*` helpers: application and
  projection shapes, binders, signatures, declaration shapes, and tactic shapes. Do not import
  another formatter module to get a helper. Move the helper to `CommonFormatters.lean` instead.
- Formatter definitions are `public def`; formatters referenced by name in `fmtWith`
  calls from other modules must be `public` as well.
- Every `Formatters/**` module shares `namespace Lean.Fmt` and they are all imported together,
  so each formatter `def` name must be **globally unique across the whole tree** — a duplicate is
  an "already declared" error. When a base name is already taken by another category's formatter
  (`fmtSorry`, `fmtSubst`, `fmtNofun`, `fmtShow`, … already exist for terms), disambiguate the new
  one, e.g. `fmtTacticSubst`, `fmtTacticShow`. Two formatters must also never register the *same*
  syntax-node kind; `@[builtin_fmt]` will not stop you, but only one wins.
- Do not add `/-! … -/` section docstrings to group formatters within a module —
  formatters are listed one after another without section headers.

## Lake formatters

The formatters for the syntax that Lake declares are in `src/lake/Lake/Formatters/`. This tree
mirrors `src/lake/Lake/`: the formatters for the syntax of `Lake.Config.Meta` are in
`Lake.Formatters.Config.Meta`. `src/lake/Lake/Formatters.lean` and the aggregation files below
it import all modules of the tree, as in the Lean tree.

The differences from the Lean tree are:

- The header uses `Copyright (c) <year> Lean FRO, LLC.` and `Authors: Marc Huisinga` (no blank
  line before it).
- After the imports, write `open Lean Lean.Fmt` and then `namespace Lake.Formatters`.
- `Lake` imports `Lake.Formatters`. A Lake module with `@[builtin_fmt]` must stay reachable by
  imports from `Lake` or `LakeMain`, because only these modules are linked into Lake's
  libraries. If it is not, its formatters do not register, and `Fmt` falls back to `fmtRaw` for
  its syntax without an error.
- `lean` does not link Lake. To see Lake's formatters with `lean` (for example, for the
  `linter.fmt.missing` linter), load Lake as a plugin with
  `--plugin=build/release/stage1/lib/lean/libLake_shared.so`.
