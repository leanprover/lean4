class Preorder (α : Type u) extends LT α :=
  (le : α → α → Prop)
  (lt_iff_le_not_le : ∀ a b : α, lt a b ↔ (le a b ∧ ¬ le b a) := by intros; rfl)

theorem Preorder.toLE_injective (A B : Preorder α) (h : A.le = B.le) (h2 : A.toLT = B.toLT) : A = B := by
  cases A; cases B; cases h
  congr
