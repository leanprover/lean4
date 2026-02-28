inductive   Tree where
  |   leaf : Nat →   Tree
  | node :   Tree → Tree →   Tree

def Tree.depth :   Tree → Nat
  |   .leaf _ => 0
  | .node   l r =>
    let dl :=   l.depth
    let dr :=   r.depth
    match   Nat.ble dl dr with
    |   true => dr + 1
    |   false => dl + 1
--^ formatting
