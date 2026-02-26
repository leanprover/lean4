structure Name where
  name : Unit

inductive Foo (Name : Type) where
| foo (x : Name)

def bar : Foo Name → Type
  | Foo.foo (Name.mk n) => Nat

def bar' : Foo Name → Type
  | Foo.foo (_root_.Name.mk n) => Nat
