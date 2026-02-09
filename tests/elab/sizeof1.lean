mutual

inductive TreePos (α : Type u) (β : Type v) where
  | leaf (a : α)
  | node (children : List (List (TreeNeg α β)))

inductive TreeNeg (α : Type u) (β : Type v) where
  | leaf (a : β)
  | node (children : List (List (TreePos α β)))

end

#print TreePos.leaf.sizeOf_spec
#print TreePos.node.sizeOf_spec
#print TreePos._sizeOf_3_eq
#print TreePos._sizeOf_4_eq
#print TreePos._sizeOf_5_eq
#print TreePos._sizeOf_6_eq
