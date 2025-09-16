module
-- set_option trace.Elab.Deriving.lawfulBEq true
-- set_option trace.Meta.MethodSpecs true

inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq

example {n m : Nat} (h : n = m) :
    (L.cons n (L.nil : L Nat) == L.cons m (L.nil : L Nat)) = true := by
  simp [reduceBEq]
  assumption

-- Module system interactions

namespace A
inductive L where | nil  : L | cons : Nat → L → L deriving BEq
-- NB: Instance, op and theorem are private
/-- info: private def A.instBEqL : BEq L -/
#guard_msgs in #print sig instBEqL
/-- info: private def A.instBEqL.beq : L → L → Bool -/
#guard_msgs in #print sig instBEqL.beq
/-- info: private theorem A.instBEqL.beq_spec_1 : (L.nil == L.nil) = true -/
#guard_msgs(pass trace, all) in #print sig instBEqL.beq_spec_1
example : (L.cons n (L.nil : L) == L.cons m (L.nil : L)) ↔ n = m := by simp [reduceBEq]
end A

namespace B
public inductive L where | nil  : L | cons : Nat → L → L deriving BEq
-- NB: Instance is public and exposed, op and theorem are private
/-- info: @[expose] def B.instBEqL : BEq L -/
#guard_msgs in #print sig instBEqL
/-- info: def B.instBEqL.beq : L → L → Bool -/
#guard_msgs in #print sig instBEqL.beq
-- NB: Private theorem
/-- info: private theorem B.instBEqL.beq_spec_1 : (L.nil == L.nil) = true -/
#guard_msgs(pass trace, all) in #print sig instBEqL.beq_spec_1
example : (L.cons n (L.nil : L) == L.cons m (L.nil : L)) ↔ n = m := by simp [reduceBEq]
end B

namespace C
public inductive L where | nil  : L | cons : Nat → L → L deriving @[expose] BEq
-- NB: Public exposed instances, implementation and public theorem
/-- info: @[expose] def C.instBEqL : BEq L -/
#guard_msgs in #print sig instBEqL
/-- info: @[expose] def C.instBEqL.beq : L → L → Bool -/
#guard_msgs in #print sig instBEqL.beq
/-- info: theorem C.instBEqL.beq_spec_1 : (L.nil == L.nil) = true -/
#guard_msgs(pass trace, all) in #print sig instBEqL.beq_spec_1
example : (L.cons n (L.nil : L) == L.cons m (L.nil : L)) ↔ n = m := by simp [reduceBEq]
end C
