inductive Vector' (α : Type u): Nat → Type u where
| nil : Vector' α 0
| cons (head : α) (tail : Vector' α n) : Vector' α (n+1)

namespace Vector'

def nth : Vector' α n → Fin n → α
  | cons x xs, ⟨0, _⟩ => x
  | cons x xs, ⟨k+1, h⟩ => xs.nth ⟨k, Nat.le_of_succ_le_succ h⟩

attribute [simp] nth
