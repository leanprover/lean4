-- Bad error message when same name is used as parameter and field
structure Foo (n : Nat) : Type := (n : Nat) -- error: invalid return type for 'Foo.mk'
