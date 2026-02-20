structure Foo where
  foo : Nat

def baz {x : _} := Foo.mk x -- works fine
example {x : _} := Foo.mk x
def qux {x : _} : Foo := Foo.mk x
example {x : _} : Foo := Foo.mk x
