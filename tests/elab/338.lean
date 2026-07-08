inductive Foo (Name : Type) where
| foo (x : Name)

structure Name' where
  name : Unit

def bar : Foo Name' → Type
| Foo.foo (_root_.Name'.mk name) => sorry
