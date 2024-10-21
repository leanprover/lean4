class A (α : Type) where
  one  : α
  zero : α

class B (α : Type) extends A α where
  add : α → α → α

class C (α : Type) extends A α where
  mul : α → α → α

set_option structure.diamondWarning false

class D (α : Type) extends B α, C α

set_option pp.all true

#print D.toB
#print D.toC
