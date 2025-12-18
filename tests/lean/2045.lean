/-!
# Test that function-valued notation can be unexpanded when overapplied
-/

def Function.comp' {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ :=
  fun x => f (g x)

variable (f : α → β) (g : β → γ) (x : α)
infixr:90 " ∘' "  => Function.comp'

#check (g ∘' f) x
