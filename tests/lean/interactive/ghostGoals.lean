-- Issue originally reported at
-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/tactic.20doesn't.20change.20primary.20goal.20state/near/488957772
class Preorder (α : Type) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

class PartialOrder (α : Type) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

instance : PartialOrder Nat where
  le := (· ≤ ·)
  le_refl := Nat.le_refl
  le_trans a b c := Nat.le_trans
  le_antisymm := by
    intro x
      -- One goal: x : Nat ⊢ ∀ (b : Nat), x ≤ b → b ≤ x → x = b
  --^ $/lean/plainGoal
