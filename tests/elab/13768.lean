module

import Lean

/-!
Regression test for https://github.com/leanprover/lean4/pull/13768.

`TransparencyMode` has five constructors (`.all`, `.default`, `.reducible`, `.instances`,
`.none`), so it needs 3 bits in the `Meta.Config` cache key. Previously only 2 bits were
allocated, so the high bit of `.none` (value `4`) overlapped with the `foApprox` bit, and
configurations differing only in `foApprox` produced the same key when `transparency = .none`.
-/

open Lean Meta

#guard
  ({ transparency := .none, foApprox := false } : Meta.Config).toConfigWithKey.key !=
  ({ transparency := .none, foApprox := true  } : Meta.Config).toConfigWithKey.key
