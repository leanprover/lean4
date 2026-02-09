import Std.Tactic.Do

open Std.Do

axiom eval_exprf' (expr state : Nat) (witness: List Nat) : Option Nat
axiom constrainEq2' (a b : Nat) : StateM Nat PUnit
axiom constrainEq2'Sound (a b:Nat) (witness: List Nat) :
  ⦃λ s => ⌜True⌝⦄
  -- ⦃λ s => ⌜eval_circuit s witness⌝⦄
  constrainEq2' a b
  ⦃⇓ r s =>
    ⌜eval_exprf' a s witness = eval_exprf' b s witness⌝⦄

-- {} constrainEq3 a b c {a == c}
noncomputable def constrainEq3' (a b c : Nat) : StateM Nat PUnit := do
  constrainEq2' a b
  constrainEq2' b c

/-- error: The goal type of `?witness` is not a proposition. It has type `Type`. -/
#guard_msgs in
theorem constrainEq3Transitive (a b c : Nat) (witness: List Nat) :
  -- ⦃λ s => ⌜eval_circuit s witness⌝ ⦄
  ⦃λ s => ⌜True⌝⦄
  constrainEq3' a b c
  ⦃⇓ r s =>
    ⌜eval_exprf' a s witness = eval_exprf' c s witness⌝⦄
  := by
  unfold constrainEq3'
  mintro H1
  mintro ∀s1
  mspec constrainEq2'Sound
  -- NOTE This gives a weird error:
  mintro ∀s2
  -- type mismatch
  -- has type
  --   Type
  -- of sort `Type 1` but is expected to have type
  --   Prop
  -- of sort `Type`
  sorry
