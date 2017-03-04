def Union {α : Prop} {β : Type} (s : α → set β) (x : β) : Prop :=
∃ i, x ∈ s i

example (y : ℕ) (t : set ℕ) : Union (λH : (∃x, x ∈ t), t) y → true
| ⟨⟨z, z_ex⟩, y_in⟩ := ⟨⟩
