structure Foo (A B: Type) where
    foo : B
    bar : Unit
    baz : True
    barf : A = B

example (p q : Foo Nat Unit) : p = q := rfl

structure Bar : Type where
    bar : True

example (p q : Bar) : p = q := rfl

example (p q : id (α → id Unit)) : p = q := rfl
