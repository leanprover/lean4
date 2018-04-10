/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/
open tactic

namespace test1
-- Recursive with props and subsingletons

constants (α β γ : Type) (P : α → Prop) (Q : β → Prop) (SS : α → Type)
          (SS_ss : ∀ (x : α), subsingleton (SS x))
          (f : Π (x : α), P x → β → SS x → γ) (p₁ p₂ : ∀ (x : α), P x) (h : β → β) (k₁ k₂ : ∀ (x : α), SS x)

attribute [instance] SS_ss

example (x₁ x₂ x₁' x₂' x₃ x₃' : α) (y₁ y₁' : β) (H : y₁ = y₁') :
f x₁ (p₁ x₁) (h $ h $ h y₁) (k₁ x₁) = f x₁ (p₂ x₁) (h $ h $ h y₁') (k₂ x₁) :=
begin
congr,
exact H,
end

end test1

namespace test2

-- Specializing to the prefix with props and subsingletons
constants (γ : Type) (f : Π (α : Type*) (β : Sort*), α → β → γ)
          (X : Type) (X_ss : subsingleton X)
          (Y : Prop)

attribute [instance] X_ss

example (x₁ x₂ : X) (y₁ y₂ : Y) : f X Y x₁ y₁ = f X Y x₂ y₂ := by congr

end test2

namespace test3
-- Edge case: goal proved by apply, not refl
constants (f : ℕ → ℕ)

example (n : ℕ) : f n = f n := by congr

end test3

namespace test4
-- Heq result

constants (α : Type) (β : α → Type) (γ : Type) (f : Π (x : α) (y : β x), γ)

example (x x' : α) (y : β x) (y' : β x') (H_x : x = x') (H_y : y == y') : f x y = f x' y' :=
begin
congr,
exact H_x,
exact H_y
end

end test4

namespace test5
-- heq in the goal
constants (α : Type) (β : α → Type) (γ : Π (x : α), β x → Type) (f : Π (x : α) (y : β x), γ x y)

example (x x' : α) (y : β x) (y' : β x') (H_x : x = x') (H_y : y == y') : f x y == f x' y' :=
begin
congr,
exact H_x,
exact H_y
end

end test5

namespace test6

variables (A : Type) (B : A → Type) (a a' : A) (b : B a) (b' : B a')

example : (⟨a, b⟩ : Σ a : A, B a) = ⟨a', b'⟩ :=
begin
  congr,
  show a = a', from sorry,
  show b == b', from sorry,
end

end test6
