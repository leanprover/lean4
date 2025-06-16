class A (α : Type) where
  one  : α
  zero : α

class B (α : Type) extends A α where
  add : α → α → α

class C (α : Type) extends A α where
  mul : α → α → α

set_option structureDiamondWarning false

def D.toC (x : Nat) := x

/-- error: 'D.toC' has already been declared -/
#guard_msgs in
class D (α : Type) extends B α, C α

class D (α : Type) extends B α, toC_1 : C α

#check D.toC_1
