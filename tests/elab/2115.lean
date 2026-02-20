class A (α : Type) where
  one : α

class B (α : Type) extends A α where
  two : α

class C (α : Type) extends A α where
  three : α

class D (α : Type) extends B α, C α

attribute [instance 10] C.toA

set_option pp.all true

def foo [D α] : A α := inferInstance -- should use `B.toA` since it has higher priority
#print foo

attribute [instance 5] B.toA

def bla [D α] : A α := inferInstance -- should use `C.toA` since it has higher priority
#print bla

attribute [-instance] C.toA

def boo [D α] : A α := inferInstance -- should use `B.toA`, `C.toA` attribute was erased
#print boo

attribute [instance 10] C.toA

def boo2 [D α] : A α := inferInstance -- should use `C.toA` since it has higher priority
#print boo2
