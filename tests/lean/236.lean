structure Foo where
  x : Nat
  b : Bool

#check { x := 10, b := true : Foo }

set_option pp.all true
#check { x := 10, b := true : Foo }

set_option pp.structure_instances true
#check { x := 10, b := true : Foo }
