set_option structure.diamondWarning false

class Foo (α : Type) extends Add α where
  zero : α

class FooComm (α : Type) extends Foo α where
  comm (a b : α) : a + b = b + a

class FooAssoc (α : Type) extends Foo α where
  assoc (a b c : α) : (a + b) + c = a + (b + c)

class FooAC (α : Type) extends FooComm α, FooAssoc α

def f [FooAssoc α] (a : α) :=
  a + a

def g [FooAC α] (a : α) :=
  f a + f a
