structure Foo where
  x : Nat
  b : Bool

#check { x := 10, b := true }

#check { x := 10, b := true : Foo }
