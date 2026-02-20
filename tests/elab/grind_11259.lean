inductive Lst (α : Type u) where
  | nil : Lst α
  | cons (head : α) (tail : Lst α) : Lst α

structure Prd (α : Type u) (β : Type v) where
  fst : α
  snd : β

example : sizeOf (@Lst.nil Nat) < sizeOf (Lst.cons 10 .nil) := by
  grind

example (a b : Nat) : sizeOf a < sizeOf { fst := a, snd := b : Prd _ _ } := by
  grind

example (a : α) (b : β) : sizeOf a < sizeOf { fst := a, snd := b : Prd _ _ } := by
  grind
