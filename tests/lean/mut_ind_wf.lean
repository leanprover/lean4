namespace Mutual

mutual
inductive Tree (α : Type u) where
  | node : TreeList α → Tree α
  | leaf : α → Tree α

inductive TreeList (α : Type u) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
end

mutual
def Tree.size : Tree α → Nat
  | Tree.node l =>
    -- see "TODO: linarith" in Init.WFTactics
    have : sizeOf l < 1 + sizeOf l := by
      rw [Nat.add_comm]
      apply Nat.lt_succ_self
    sizeList l
  | Tree.leaf _ => 1

def Tree.sizeList : TreeList α → Nat
  | TreeList.nil => 0
  | TreeList.cons t l =>
    have : sizeOf t < 1 + sizeOf t + sizeOf l := by
      rw [Nat.add_comm 1, Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]
      apply Nat.lt_succ_of_le
      apply Nat.le_add_right
    have : sizeOf l < 1 + sizeOf t + sizeOf l := by
      rw [Nat.add_comm 1, Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]
      apply Nat.lt_succ_of_le
      apply Nat.le_add_left
    t.size + sizeList l
end
-- use automatically synthesized size function, which is not quite the number of leaves
termination_by
  size t => sizeOf t
  sizeList l => sizeOf l

end Mutual

namespace Nested

inductive Tree (α : Type u) where
  | node : List (Tree α) → Tree α
  | leaf : α → Tree α

mutual
def Tree.size : Tree α → Nat
  | Tree.node l =>
    have : sizeOf l < 1 + sizeOf l := by
      rw [Nat.add_comm]
      apply Nat.lt_succ_self
    sizeList l
  | Tree.leaf _ => 1

def Tree.sizeList : List (Tree α) → Nat
  | [] => 0
  | t :: l =>
    have : sizeOf t < 1 + sizeOf t + sizeOf l := by
      rw [Nat.add_comm 1, Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]
      apply Nat.lt_succ_of_le
      apply Nat.le_add_right
    have : sizeOf l < 1 + sizeOf t + sizeOf l := by
      rw [Nat.add_comm 1, Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]
      apply Nat.lt_succ_of_le
      apply Nat.le_add_left
    t.size + sizeList l
end
termination_by
  size t => sizeOf t
  sizeList l => sizeOf l

end Nested
