inductive Foo
  | foo | bar

def baz (b : Bool) (x : Foo := .foo) : Foo := Id.run <| do
  let mut y := x
  if b then
    y := .bar
  y
