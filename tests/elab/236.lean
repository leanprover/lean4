structure Foo where
  x : Nat
  b : Bool

#check { x := 10, b := true : Foo }

set_option pp.all true
#check { x := 10, b := true : Foo }

set_option pp.universes false
set_option pp.explicit false
set_option pp.structureInstances true
#check { x := 10, b := true : Foo }
