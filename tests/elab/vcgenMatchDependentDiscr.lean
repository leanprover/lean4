import Std.WP

set_option sym.debug true

/-!
Regression test for `vcgen` splitting a `match` whose discriminant telescope is
dependent: a later discriminant's type mentions an earlier discriminant. Abstracting the matcher
introduces the discriminant fvars as a dependent telescope, substituting each earlier original
discriminant with its abstract counterpart, so the pre-splitter motive stays type-correct.
-/

set_option experimental.vcgen true

/-- The second discriminant `h : 0 < n` mentions the first discriminant `n`. -/
def prog (n : Nat) (h : 0 < n) : StateM Nat Unit := do
  match n, h with
  | m+1, _ => set m

section
open Lean.Order Std.WP

example (n : Nat) (h : 0 < n) :
    ⦃fun _ => True⦄ prog n h ⦃fun _ _ => True⦄ := by
  unfold prog
  vcgen
  all_goals simp_all
end
