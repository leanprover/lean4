structure Foo := (foo : unit)

def my_foo : Foo := Foo.mk ()
@[simp] lemma my_foo.def : my_foo = Foo.mk () := rfl

example : Foo.foo my_foo = () := by dsimp
