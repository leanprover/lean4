import Lean

/-!
Regression test for #14919: `simprocCore` collects all simproc candidates for an expression up
front, each with the number of trailing arguments to peel off before running it. A simproc that
returns `.continue` with a smaller expression used to leave those counts stale, so the next
candidate panicked in `Expr.appArg!`/`Expr.appFn!`.
-/

open Lean Meta Simp

private def foo (_a _b : Nat) : Nat := 0

/-- Rewrites the whole application to a term that is not an application. -/
simproc shrink (foo _ _) := fun _ => return .continue (some { expr := mkRawNatLit 0 })

/-- Selected as a candidate for the prefix `foo 1`, that is, with one extra argument. -/
simproc prefixKey (foo _) := fun _ => return .continue

set_option linter.unusedSimpArgs false in
example : foo 1 2 = 0 := by simp only [shrink, prefixKey]
