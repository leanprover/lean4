variable (f : α → β) (g : β → γ) (x : α)
infixr:90 " ∘' "  => Function.comp

#check (g ∘' f) x
