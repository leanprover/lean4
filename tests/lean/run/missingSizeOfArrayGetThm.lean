inductive Node (Data : Type) : Type where
| empty : Node Data
| node  (children : Array (Node Data)) : Node Data
| leaf  (data : Data) : Node Data

def Node.FixedBranching (n : Nat) : Node Data → Prop
  | empty => True
  | node children => children.size = n ∧ ∀ i, (children.get i).FixedBranching n
  | leaf _ => True
decreasing_by
  simp_wf
  apply Nat.lt_trans (Array.sizeOf_get ..) -- TODO: remove after we add linarith
  simp_arith

structure MNode (Data : Type) (m : Nat) where
  node : Node Data
  fix_branching : node.FixedBranching m
