inductive Node (Data : Type) : Type where
| empty : Node Data
| node  (children : Array (Node Data)) : Node Data
| leaf  (data : Data) : Node Data

def Node.FixedBranching (n : Nat) : Node Data → Prop
  | empty => True
  | node children => children.size = n ∧ ∀ (i : Nat) h, (children[i]'h).FixedBranching n
  | leaf _ => True

structure MNode (Data : Type) (m : Nat) where
  node : Node Data
  fix_branching : node.FixedBranching m
