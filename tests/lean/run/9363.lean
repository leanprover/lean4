import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

axiom P : Nat → Prop
axiom P' : Nat → Prop
axiom Q : Nat → Prop
axiom R : Assertion ps

axiom hPQ : ∀ n, P n → P' n → Q n

axiom G : StateM Nat Unit
axiom H : StateM Nat Unit

noncomputable def F : StateM Nat Unit := do
  G
  H

@[spec]
axiom G_spec : ⦃⌜True⌝⦄ G ⦃⇓ _ n => ⌜P n ∧ P' n⌝⦄

@[spec]
axiom H_spec : ⦃fun n => ⌜Q n⌝⦄ H ⦃⇓ _ => R⦄

theorem F_spec :
   ⦃⌜True⌝⦄
   F
   ⦃⇓ _ => R⦄ := by
  mvcgen [F]

  -- Goal:
  -- s✝¹ : Nat
  -- r✝ : Unit
  -- s✝ : Nat
  -- h : P s✝ ∧ P' s✝
  -- ⊢ Q s✝

  rename_i h
  cases h
  apply hPQ
  assumption
  assumption
