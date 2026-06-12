module

import Lean

/-!
Regression test for https://github.com/leanprover/lean4/issues/13770.

`Meta.Config.zetaUnused` controls `whnfCore`/`isDefEqQuick` reduction of unused `let`/`have`
bindings, so two configs differing only in `zetaUnused` must produce distinct cache keys.
-/

open Lean Meta

#guard
  ({ zetaUnused := false } : Meta.Config).toConfigWithKey.key !=
  ({ zetaUnused := true  } : Meta.Config).toConfigWithKey.key
