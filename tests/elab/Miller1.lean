class HasMulComm (α : Type u) [Mul α] : Prop where
    mulComm : {a b : α} → a * b = b * a

class A (α : Type u) extends Mul α
attribute [instance] A.mk

class B (α : Type u) extends A α, HasMulComm α
attribute [instance] B.mk

example [Mul α] : A α := inferInstance
example [Mul α] [HasMulComm α] : A α := inferInstance
example [B α] : A α := inferInstance

example [A α] [HasMulComm α] : B α := inferInstance
example [Mul α] [HasMulComm α] : B α := inferInstance
example [Mul α] [HasMulComm α] : B α := B.mk
