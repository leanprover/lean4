inductive Tree (β : Type v) where
  | leaf
  | node (left : Tree β) (key : Nat) (value : β) (right : Tree β)
  deriving Repr

inductive ForallTree (p : Nat → β → Prop) : Tree β → Prop
  | leaf : ForallTree p .leaf
  | node :
     ForallTree p left →
     p key value →
     ForallTree p right →
     ForallTree p (.node left key value right)

inductive BST : Tree β → Prop
  | leaf : BST .leaf
  | node :
     ForallTree (fun k v => k < key) left →
     ForallTree (fun k v => key < k) right →
     BST left → BST right →
     BST (.node left key value right)

#print BST
