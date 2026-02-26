inductive Arrow : Type → Type → Type 1
  | id   : Arrow a a
  | unit : Arrow Unit Unit
  | comp : Arrow β γ → Arrow α β → Arrow α γ
deriving Repr

def Arrow.compose (f : Arrow β γ) (g : Arrow α β) : Arrow α γ :=
  match f, g with
  | id, g => g
  | f, id => f
  | f, g => comp f g

#eval Arrow.compose Arrow.unit Arrow.id
