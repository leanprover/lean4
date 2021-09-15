--
set_option autoBoundImplicitLocal false
universe u
variable {α : Type u}
variable {β : α → Type v}
infix:50 " ≅ " => HEq
theorem ex {p₁ p₂ : Sigma (fun a => β a)} (h₁ : p₁.1 = p₂.1) (h : p₁.2 ≅ p₂.2) : p₁ = p₂ :=
match p₁, p₂, h₁, h with
| ⟨_, _⟩, ⟨_, _⟩, rfl, HEq.refl _ => rfl
