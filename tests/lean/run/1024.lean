inductive Vector' (α : Type u): Nat → Type u where
| nil : Vector' α 0
| cons (head : α) (tail : Vector' α n) : Vector' α (n+1)

namespace Vector'
  def nth : ∀{n}, Vector' α n → Fin n → α
  | n+1, cons x xs, ⟨  0, _⟩ => x
  | n+1, cons x xs, ⟨k+1, h⟩ => xs.nth ⟨k, sorry⟩

  def snoc : ∀{n : Nat} (xs : Vector' α n) (x : α), Vector' α (n+1)
  | _, nil,    x' => cons x' nil
  | _, cons x xs, x' => cons x (snoc xs x')

  theorem nth_snoc_eq (k: Fin (n+1))(v : Vector' α n)
    (h: k.val = n):
    (v.snoc x).nth k = x := by
    cases k; rename_i k hk
    induction v generalizing k <;> subst h
    · simp only [nth]
    · simp! [*]

  theorem nth_snoc_eq_works (k: Fin (n+1))(v : Vector' α n)
    (h: k.val = n):
    (v.snoc x).nth k = x := by
    cases k; rename_i k hk
    induction v generalizing k <;> subst h
    · simp only [nth]
    · simp[*,nth]
end Vector'
