inductive Foo where
  | foo
--^ waitForILeans
example : Foo :=
  let c := Foo.foo
  c
--^ textDocument/typeDefinition

def f (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | y + 1 => y
           --^ textDocument/declaration
