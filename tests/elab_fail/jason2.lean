inductive Foo {x : Nat} : Type where
  | foo : Foo

def bar := (fun _ : Foo => 0) Foo.foo
