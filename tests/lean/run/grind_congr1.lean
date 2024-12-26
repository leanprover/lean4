import Lean

open Lean Meta Elab Tactic Grind in
elab "grind_test" : tactic => withMainContext do
  let declName := (← Term.getDeclName?).getD `_main
  Meta.Grind.preprocessAndProbe (← getMainGoal) declName do
    unless (← isInconsistent) do
      throwError "inconsistent state expected"

set_option grind.debug true
set_option grind.debug.proofs true

example (a b : Nat) (f : Nat → Nat) : (h₁ : a = b) → f a = f b := by
  grind_test
  sorry

example (a b : Nat) (f : Nat → Nat) : (h₁ : a = b) → (h₂ : f a ≠ f b) → False := by
  grind_test
  sorry

example (a b : Nat) (f : Nat → Nat) : a = b → f (f a) ≠ f (f b) → False := by
  grind_test
  sorry

example (a b c : Nat) (f : Nat → Nat) : a = b → c = b → f (f a) ≠ f (f c) → False := by
  grind_test
  sorry

example (a b c : Nat) (f : Nat → Nat → Nat) : a = b → c = b → f (f a b) a ≠ f (f c c) c → False := by
  grind_test
  sorry

example (a b c : Nat) (f : Nat → Nat → Nat) : a = b → c = b → f (f a b) a = f (f c c) c := by
  grind_test
  sorry

example (a b c d : Nat) : a = b → b = c → c = d → a = d := by
  grind_test
  sorry

infix:50 "===" => HEq

example (a b c d : Nat) : a === b → b = c → c === d → a === d := by
  grind_test
  sorry

example (a b c d : Nat) : a = b → b = c → c === d → a === d := by
  grind_test
  sorry

opaque f {α : Type} : α → α → α := fun a _ => a
opaque g : Nat → Nat

example (a b c : Nat) : a = b → g a === g b := by
  grind_test
  sorry

example (a b c : Nat) : a = b → c = b → f (f a b) (g c) = f (f c a) (g b) := by
  grind_test
  sorry

example (a b c d e x y : Nat) : a = b → a = x → b = y → c = d → c = e → c = b → a = e := by
  grind_test
  sorry

namespace Ex1
opaque f (a b : Nat) : a > b → Nat
opaque g : Nat → Nat

example (a₁ a₂ b₁ b₂ c d : Nat)
        (H₁ : a₁ > b₁)
        (H₂ : a₂ > b₂) :
        a₁ = c → a₂ = c →
        b₁ = d → d  = b₂ →
        g (g (f a₁ b₁ H₁)) = g (g (f a₂ b₂ H₂)) := by
  grind_test
  sorry
end Ex1

namespace Ex2
def f (α : Type) (a : α) : α := a

example (a : α) (b : β) : (h₁ : α = β) → (h₂ : HEq a b) → HEq (f α a) (f β b) := by
  grind_test
  sorry

end Ex2

example (f g : (α : Type) → α → α) (a : α) (b : β) : (h₁ : α = β) → (h₂ : HEq a b) → (h₃ : f = g) → HEq (f α a) (g β b) := by
  grind_test
  sorry

set_option trace.grind.proof true in
set_option trace.grind.proof.detail true in
example (f : {α : Type} → α → Nat → Bool → Nat) (a b : Nat) : f a 0 true = v₁ → f b 0 true = v₂ → a = b → v₁ = v₂ := by
  grind_test
  sorry

set_option trace.grind.proof true in
set_option trace.grind.proof.detail true in
example (f : {α : Type} → α → Nat → Bool → Nat) (a b : Nat) : f a b x = v₁ → f a b y = v₂ → x = y → v₁ = v₂ := by
  grind_test
  sorry

set_option trace.grind.proof true in
set_option trace.grind.proof.detail true in
example (f : {α : Type} → α → Nat → Bool → Nat) (a b c : Nat) : f a b x = v₁ → f c b y = v₂ → a = c → x = y → v₁ = v₂ := by
  grind_test
  sorry
