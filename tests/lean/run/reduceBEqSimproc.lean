module
-- set_option trace.Elab.Deriving.lawfulBEq true
-- set_option trace.Meta.MethodSpecs true

set_option deriving.beq.linear_construction_threshold 1000

inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq

example {n m : Nat} (h : n = m) :
    (L.cons n (L.nil : L Nat) == L.cons m (L.nil : L Nat)) = true := by
  simp [reduceBEq]
  assumption

-- Linear construction

namespace Linear

set_option deriving.beq.linear_construction_threshold 0

inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq

-- This should still split the equations

/--
info: Linear.instBEqL.beq.eq_1.{u_1} {α✝ : Type u_1} [BEq α✝] (x✝ x✝¹ : L α✝) :
  instBEqL.beq x✝ x✝¹ =
    match decEq x✝.ctorIdx x✝¹.ctorIdx with
    | { decide := true, reflects_decide := h } =>
      match x✝, x✝¹, h with
      | L.nil, L.nil, ⋯ => true
      | L.cons a a_1, L.cons a' a'_1, ⋯ => a == a' && instBEqL.beq a_1 a'_1
    | { decide := false, reflects_decide := reflects_decide } => false
-/
#guard_msgs in
#check instBEqL.beq.eq_1

-- And this should work without L.ctorIdx

example {n m : Nat} (h : n = m) :
    (L.cons n (L.nil : L Nat) == L.cons m (L.nil : L Nat)) = true := by
  simp [reduceBEq, reduceCtorIdx]
  assumption

end Linear

-- Module system interactions

namespace A
inductive L where | nil  : L | cons : Nat → L → L deriving BEq
-- NB: Instance, op and theorem are private
/-- info: @[instance_reducible] private def A.instBEqL : BEq L -/
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
/-- info: @[instance_reducible, expose] def B.instBEqL : BEq L -/
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
/-- info: @[instance_reducible, expose] def C.instBEqL : BEq L -/
#guard_msgs in #print sig instBEqL
/-- info: @[expose] def C.instBEqL.beq : L → L → Bool -/
#guard_msgs in #print sig instBEqL.beq
/-- info: theorem C.instBEqL.beq_spec_1 : (L.nil == L.nil) = true -/
#guard_msgs(pass trace, all) in #print sig instBEqL.beq_spec_1
example : (L.cons n (L.nil : L) == L.cons m (L.nil : L)) ↔ n = m := by simp [reduceBEq]
end C
