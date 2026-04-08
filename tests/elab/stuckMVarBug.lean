class HasMulComm (α : Type u) [Mul α] : Prop where
    mulComm : {a b : α} → a * b = b * a

class A (α : Type u) where
    [Mul : Mul α]
attribute [instance] A.mk A.Mul

class B (α : Type u) where
    [Mul : Mul α]
    [HasMulComm : HasMulComm α]
attribute [instance] B.mk B.Mul B.HasMulComm

example [A α] [HasMulComm α] : B α := inferInstance

section
variable [A α] [HasMulComm α]

example : B α := by exact inferInstance

example : B α := inferInstance

end
