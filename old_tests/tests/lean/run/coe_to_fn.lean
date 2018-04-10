universes u v w

structure equiv (α : Type u) (β : Type v) :=
(f : α → β) (g : β → α)

infix ` ≃ `:50 := equiv

variables {α : Type u} {β : Type v} {γ : Type w}

instance: has_coe_to_fun (α ≃ β) := {
    F := λ _, α → β,
    coe := equiv.f,
}

@[symm] def equiv.inv : α ≃ β → β ≃ α
| ⟨f,g⟩ := ⟨g,f⟩

local postfix `⁻¹` := equiv.inv

-- coe_fn should be applied at function arguments
def equiv.trans (f : α ≃ β) (g : β ≃ γ) : α ≃ γ :=
⟨g ∘ f, f⁻¹ ∘ g⁻¹⟩

example (f : α ≃ β) := function.bijective f
example (f : α ≃ β) (a : α) := f a
example (f : (α ≃ β) ≃ (β ≃ α)) (g : α ≃ β) (b : β) := f g b