import Lean

/-!
# Test: projection functions have `.abbrev` kernel hints

All projection functions receive `.abbrev` kernel hints at creation time.
Structure projections default to `.reducible` status, while class projections
default to `.semireducible` status. The `@[reducible]` attribute changes the
reducibility status but does **not** change the kernel hint.

These properties are relied upon by `isNonTrivialRegular` in `ExprDefEq.lean`.
That function uses the `.abbrev` branch to detect class projections and treat
them as nontrivial when `backward.whnf.reducibleClassField` is enabled, so that
`tryHeuristic` applies the argument-comparison heuristic (with the correct
transparency bump for instance-implicit parameters) instead of unfolding past
the `.proj` form. If the kernel hints or default reducibility status for
projections change, `isNonTrivialRegular` must be updated accordingly.
-/

structure Y where
  x : Nat

class X where
  x : Nat

open Lean
deriving instance Repr for ReducibilityHints

def showHintAndReduceAttr (declName : Name) : CoreM Unit := do
  let info ← getConstInfo declName
  IO.println (repr info.hints)
  IO.println (repr (← getReducibilityStatus declName))

-- Structure projection: `.abbrev` hint, `.reducible` status
/--
info: Lean.ReducibilityHints.abbrev
Lean.ReducibilityStatus.reducible
-/
#guard_msgs in
#eval showHintAndReduceAttr ``Y.x

-- Class projection: `.abbrev` hint, `.semireducible` status
/--
info: Lean.ReducibilityHints.abbrev
Lean.ReducibilityStatus.semireducible
-/
#guard_msgs in
#eval showHintAndReduceAttr ``X.x
