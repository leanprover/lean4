import Std.Tactic.Do

set_option sym.debug true

/-!
Regression test for the deprecated `mvcgen` tactic splitting a `match` whose discriminant
telescope is dependent: a later discriminant's type mentions an earlier discriminant. The `vcgen`
version of this test is `tests/elab/vcgenMatchDependentDiscr.lean`.
-/

/-- The second discriminant `h : 0 < n` mentions the first discriminant `n`. -/
def prog (n : Nat) (h : 0 < n) : StateM Nat Unit := do
  match n, h with
  | m+1, _ => set m

open Std.Do

example (n : Nat) (h : 0 < n) :
    ⦃⌜True⌝⦄ prog n h ⦃⇓ _ => ⌜True⌝⦄ := by
  unfold prog
  mvcgen
  all_goals simp_all
