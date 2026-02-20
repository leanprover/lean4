structure A where
  x : Nat
  y : Nat

namespace Foo

scoped instance : ToString A where
  toString a := s!"A.mk {a.x} {a.y}"

end Foo

#eval toString { x := 10, y := 20 : A } -- Error: failed to synthesize `ToString A`

section Sec1
open Foo

#eval toString { x := 10, y := 20 : A } -- works

end Sec1 -- scoped instance `ToString A` is not available anymore

#eval toString { x := 10, y := 20 : A } -- Error

section Sec2

local instance : ToString A where
  toString a := s!"\{ x := {a.x}, y := {a.y} }"

#eval toString { x := 10, y := 20 : A } -- works, using local instance

end Sec2 -- local instance `ToString A` is not available anymore

#eval toString { x := 10, y := 20 : A } -- Error

open Foo

#eval toString { x := 10, y := 20 : A } -- works
