import Std.Tactic.Do
import Std.Internal.Do

/-!
Regression test for `mvcgen`/`vcgen` splitting a `match` whose discriminant telescope is
dependent: a later discriminant's type mentions an earlier discriminant. Abstracting the matcher
introduces the discriminant fvars as a dependent telescope, substituting each earlier original
discriminant with its abstract counterpart, so the pre-splitter motive stays type-correct.
-/

set_option mvcgen.warning false

/-- The second discriminant `h : 0 < n` mentions the first discriminant `n`. -/
def prog (n : Nat) (h : 0 < n) : StateM Nat Unit := do
  match n, h with
  | m+1, _ => set m

section
open Lean.Order Std.Internal.Do

example (n : Nat) (h : 0 < n) :
    ⦃fun _ => True⦄ prog n h ⦃fun _ _ => True⦄ := by
  unfold prog
  vcgen
  all_goals simp_all
end

-- Separate section: `Std.Do`'s `⦃ ⦄` notation clashes with the one above.
section
open Std.Do

example (n : Nat) (h : 0 < n) :
    ⦃⌜True⌝⦄ prog n h ⦃⇓ _ => ⌜True⌝⦄ := by
  unfold prog
  mvcgen
  all_goals simp_all
end
