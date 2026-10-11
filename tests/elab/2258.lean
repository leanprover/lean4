/-! Checks that the criteria for unit-like types handles all appropriate types, i.e foralls whose codomains are unit-like types, and (non-recursive) structures whose fields are alleither unit-like or propositions.-/

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
