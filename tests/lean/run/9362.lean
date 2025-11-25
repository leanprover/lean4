import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

axiom G (lt : Nat) : Id Unit

noncomputable def F : Id Unit := do
  G 1

axiom P : Prop

@[spec]
axiom G_spec (h : P) :
   ⦃⌜True⌝⦄ G 1 ⦃⇓ _ => ⌜0 < 1⌝⦄

theorem F_spec (h : P) :
   ⦃⌜True⌝⦄ F ⦃⇓ _ => ⌜0 < 1⌝⦄ := by
  mvcgen [F] -- should close (h : P ⊢ P) by trivial
