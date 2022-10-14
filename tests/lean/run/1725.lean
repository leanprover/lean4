structure Fun (α β : Type) : Type where
  toFun : α → β

instance : CoeFun (Fun α β) (fun _ => α → β) where
  coe := Fun.toFun

example (f : Fun α α) : α → α :=
  f ∘ f

example (f : Fun α β) : (γ δ : Type) × (γ → δ) :=
  ⟨_, _, f⟩

structure Equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix:25 " ≃ " => Equiv

variable {α β γ : Sort _}

instance : CoeFun (α ≃ β) (λ _ => α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

protected def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
