open sigma.ops

section
  parameter A : Type
  parameter C : A → Type
  parameter P : ∀ a, C a → Prop

  example
    (x t : A)
    (e  : x = t)
    (h₁ : C x)
    (h₂ : P x h₁)
    : unit :=
    obtain (nh₁  : C t) (nh₂ : P t nh₁), from eq.rec_on e ⟨h₁, h₂⟩,
    unit.star
end
