import data.sum data.nat
open function

structure equiv [class] (A B : Type) :=
  (to_fun    : A → B)
  (inv_fun   : B → A)
  (left_inv  : left_inverse inv_fun to_fun)
  (right_inv : right_inverse inv_fun to_fun)

namespace equiv
infix ` ≃ `:50 := equiv

protected definition refl [refl] (A : Type) : A ≃ A :=
mk (@id A) (@id A) (λ x, rfl) (λ x, rfl)

protected definition symm [symm] {A B : Type} : A ≃ B → B ≃ A
| (mk f g h₁ h₂) := mk g f h₂ h₁

protected definition trans [trans] {A B C : Type} : A ≃ B → B ≃ C → A ≃ C
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk (f₂ ∘ f₁) (g₁ ∘ g₂)
   (show ∀ x, g₁ (g₂ (f₂ (f₁ x))) = x, by intros; rewrite [l₂, l₁]; reflexivity)
   (show ∀ x, f₂ (f₁ (g₁ (g₂ x))) = x, by intros; rewrite [r₁, r₂]; reflexivity)

definition arrow_congr₁ {A₁ A₂ B₁ B₂ : Type} : A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ → B₁) ≃ (A₂ → B₂)
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk
   (λ (h : A₁ → B₁) (a : A₂), f₂ (h (g₁ a)))
   (λ (h : A₂ → B₂) (a : A₁), g₂ (h (f₁ a)))
   (λ h, funext (λ a, begin rewrite [l₁, l₂], reflexivity end))
   (begin unfold [left_inverse, right_inverse] at *, intros, apply funext, intros, simp end)

local attribute left_inverse right_inverse [reducible]

definition arrow_congr₂ {A₁ A₂ B₁ B₂ : Type} : A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ → B₁) ≃ (A₂ → B₂)
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk (λ h a, f₂ (h (g₁ a))) (λ h a, g₂ (h (f₁ a))) (by simp) (by simp)

end equiv
