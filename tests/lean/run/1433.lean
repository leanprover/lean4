protected def num_denum := ℤ × {d:ℤ // d > 0}

protected def rel : num_denum → num_denum → Prop
| ⟨n₁, ⟨d₁, _⟩⟩ ⟨n₂, ⟨d₂, _⟩⟩ := n₁ = n₂

example : ∀(a : num_denum), rel a a :=
λ⟨n₁, ⟨d₁, h₁⟩⟩, show n₁ = n₁, begin [smt] end
