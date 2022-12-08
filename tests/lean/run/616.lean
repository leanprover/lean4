def bug : Monad (λ α : Type _ => α → Prop) where
  pure x := (.=x)
  bind s f y := ∃ x, s x ∧ f x y
