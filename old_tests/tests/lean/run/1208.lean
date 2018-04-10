lemma foo {α : Type*} {f : α → α} (a : α) : f a = f a := rfl
example {X : Type} (h : X → X) (x₀ : X) : h x₀ = h x₀ := by apply (foo x₀)
