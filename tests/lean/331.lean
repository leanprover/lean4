structure Foo where
  foo : Nat

def baz {x : _} := Foo.mk x -- works fine

def qux {x : _} : Foo := Foo.mk x
