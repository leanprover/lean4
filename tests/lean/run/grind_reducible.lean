variable {α β γ : Type}

structure Equiv (α β : Type) where
  toFun : α → β
  invFun : β → α

infixl:25 " ≃ " => Equiv

namespace Equiv

instance : CoeFun (α ≃ β) (fun _ => α → β) := ⟨toFun⟩

@[ext, grind ext] theorem ext {f g : Equiv α β} (H : ∀ x, f x = g x) : f = g := sorry

theorem congr_fun {f g : Equiv α β} (h : f = g) (x : α) : f x = g x := by rw [h]

def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ := ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

def sigmaCongrRight {α : Type} {β₁ β₂ : α → Type} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ a, β₁ a) ≃ Σ a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩

def sigmaEquivProd (α β : Type) : (Σ _ : α, β) ≃ α × β where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

end Equiv

variable {α₁ β₁ β₂ : Type} (e : α₁ → β₁ ≃ β₂)

def prodCongrRight : α₁ × β₁ ≃ α₁ × β₂ where
  toFun ab := ⟨ab.1, e ab.1 ab.2⟩
  invFun ab := ⟨ab.1, (e ab.1).symm ab.2⟩

example :
    (Equiv.sigmaCongrRight e).trans (Equiv.sigmaEquivProd α₁ β₂)
    = (Equiv.sigmaEquivProd α₁ β₁).trans (prodCongrRight e) := by
  grind -reducible only [Equiv.congr_fun]

example :
    (Equiv.sigmaCongrRight e).trans (Equiv.sigmaEquivProd α₁ β₂)
    = (Equiv.sigmaEquivProd α₁ β₁).trans (prodCongrRight e) := by
  grind -reducible only => finish only [Equiv.congr_fun]

example :
    (Equiv.sigmaCongrRight e).trans (Equiv.sigmaEquivProd α₁ β₂)
    = (Equiv.sigmaEquivProd α₁ β₁).trans (prodCongrRight e) := by
  grind -reducible => cases #d592 <;> instantiate only [Equiv.congr_fun]

/--
info: Try these:
  [apply] grind -reducible only [Equiv.congr_fun, #d592]
  [apply] grind -reducible only [Equiv.congr_fun]
  [apply] grind -reducible => cases #d592 <;> instantiate only [Equiv.congr_fun]
-/
#guard_msgs in
example :
    (Equiv.sigmaCongrRight e).trans (Equiv.sigmaEquivProd α₁ β₂)
    = (Equiv.sigmaEquivProd α₁ β₁).trans (prodCongrRight e) := by
  grind? -reducible [Equiv.congr_fun]
