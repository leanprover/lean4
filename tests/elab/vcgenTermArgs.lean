import Std.Internal.Do
import Std.Tactic.Do

/-!
Tests that `vcgen [...]` accepts arbitrary term arguments, mirroring `simp [...]`.
A term proving a Hoare triple / `⊑ wp` spec is registered as a spec; any other proof is
handled as a simp lemma (equation), exactly as `simp` would.
-/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do

/-! Equation term argument: `show lhs = rhs from h` rewrites an opaque program action. -/
section
opaque act : StateM Nat Unit

example (h : act = pure ()) :
    ⦃fun (_ : Nat) => True⦄ act ⦃fun _ _ => True⦄ := by
  vcgen [show act = pure () from h] with finish
end

/-! Spec proof term argument built by a partially applied identifier `gspec 0`. -/
section
set_option warn.sorry false
axiom G : StateM Nat Unit
axiom gspec (n : Nat) : ⦃fun (_ : Nat) => True⦄ G ⦃fun _ m => m = m⦄

example : ⦃fun (_ : Nat) => True⦄ G ⦃fun _ m => m = m⦄ := by
  vcgen [gspec 0]
end

/-! Regression: a `def`'s equation as a bare identifier, and the same equation as the
non-identifier term `@dep.eq_def`. -/
section
def dep (n : Option Nat) : Id Nat :=
  match _h : n with | some y => pure (y + 1) | none => pure 2

example (n : Option Nat) : ⦃ True ⦄ dep n ⦃ fun r => r > 0 ⦄ := by
  vcgen [dep.eq_def] with finish

example (n : Option Nat) : ⦃ True ⦄ dep n ⦃ fun r => r > 0 ⦄ := by
  vcgen [@dep.eq_def] with finish
end
