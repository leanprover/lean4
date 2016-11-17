def id₁ {'a : Type} (x : 'a) : 'a := x

def id₂ {α : Type} (a : α) : α := a

def id₃ {β : Type} (b : β) : β := b

check λ (α β : Type) (f : α → β) (a : α), f a

check λ ('a 'b : Type) (f : 'a → 'b) (a : 'a), f a
