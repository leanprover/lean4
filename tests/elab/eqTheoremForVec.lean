inductive Vector' (α : Type u): Nat → Type u where
| nil : Vector' α 0
| cons (head : α) (tail : Vector' α n) : Vector' α (n+1)

def Vector'.nth : ∀{n}, Vector' α n → Fin n → α
| n+1, Vector'.cons x xs, ⟨  0, _⟩ => x
| n+1, Vector'.cons x xs, ⟨k+1, h⟩ => xs.nth ⟨k, Nat.lt_of_add_lt_add_right h⟩
