/- Inductive Types -/

inductive Tree (β : Type v) where
  | leaf
  | node (left : Tree β) (key : Nat) (value : β) (right : Tree β)
  deriving Repr

#eval Tree.node .leaf 10 true .leaf
-- Tree.node Tree.leaf 10 true Tree.leaf

inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → Vector α n → Vector α (n+1)

