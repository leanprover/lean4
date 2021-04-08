inductive Foo where
  | foo
example : Foo :=
  let c := Foo.foo
  c
--^ textDocument/typeDefinition
