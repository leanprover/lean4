set_option deriving.beq.linear_construction_threshold 1000

inductive L (α : Type) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq, Ord

/--
info: theorem instBEqL.beq_spec_2 : ∀ {α : Type} [inst : BEq α] (a : α) (a_1 : L α) (b : α) (b_1 : L α),
  (L.cons a a_1 == L.cons b b_1) = (a == b && a_1 == b_1)
-/
#guard_msgs in
#print sig instBEqL.beq_spec_2

-- Ord does not support recursive types yet:

/-- error: Unknown constant `instOrdL.compare_spec_2` -/
#guard_msgs in
#print sig instOrdL.compare_spec_2

inductive O (α : Type u) where
  | none
  | some : α → O α
deriving BEq, Ord

/--
info: theorem instBEqO.beq_spec_2.{u_1} : ∀ {α : Type u_1} [inst : BEq α] (a b : α), (O.some a == O.some b) = (a == b)
-/
#guard_msgs in #print sig instBEqO.beq_spec_2
/--
info: theorem instOrdO.compare_spec_1.{u_1} : ∀ {α : Type u_1} [inst : Ord α], compare O.none O.none = Ordering.eq
-/
#guard_msgs in #print sig instOrdO.compare_spec_1
/--
info: theorem instOrdO.compare_spec_2.{u_1} : ∀ {α : Type u_1} [inst : Ord α] (x : O α),
  (x = O.none → False) → compare O.none x = Ordering.lt
-/
#guard_msgs in #print sig instOrdO.compare_spec_2
/--
info: theorem instOrdO.compare_spec_4.{u_1} : ∀ {α : Type u_1} [inst : Ord α] (a b : α),
  compare (O.some a) (O.some b) = (compare a b).then Ordering.eq
-/
#guard_msgs in #print sig instOrdO.compare_spec_4

-- Mutual inductive (not supported yet, but should be)

mutual
inductive Tree (α : Type) where
  | node : TreeList α → Tree α
  deriving BEq
inductive TreeList (α : Type) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
  deriving BEq
end


/-- error: Unknown constant `instBEqTree.beq_spec_1` -/
#guard_msgs in
#print sig instBEqTree.beq_spec_1
