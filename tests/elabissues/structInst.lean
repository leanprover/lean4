namespace Ex1

structure A :=
(x : Nat)

structure B extends A :=
(y : Nat := x + 2) (x := y + 1)

structure C extends B :=
(z : Nat) (x := z + 10)

#check { y := 1 : B } -- works
#check { z := 1 : C } -- doesn't work, expected { z := 1, x := 1 + 10, y := (1 + 10) + 2 }

end Ex1

namespace Ex2

structure A :=
(x : Nat) (y : Nat)

structure B extends A :=
(z : Nat := x + 1) (y := z + x)

#print B.y._default

#check { x := 1 : B } -- works, but reduced a `Add.add` into `Nat.add`:  `{toA := {x := 1, y := Nat.add (1+1) 1}, z := 1+1} : B`.

end Ex2

namespace Ex3

structure A :=
(x : Nat)

structure B extends A :=
(y : Nat := x + 2) (x := y + 1)

structure C extends B :=
(z : Nat := 2*y) (x := z + 2) (y := z + 3)

#check { x := 1 : C } -- doesn't work, should be { x := 1, y := 1+2, z := 2*(1+2) }
#check { y := 1 : C } -- doesn't work, should be { y := 1, z := 2*1, x := 2*1 + 2 }
#check { z := 1 : C } -- doesn't work, should be { z := 1, x := 1 + 2, y := 1 + 3 }

end Ex3

namespace Ex4

structure A :=
(x : Nat)

structure B extends A :=
(y : Nat := x + 1) (x := y + 1)

structure C extends B :=
(z : Nat := 2*y) (x := z + 3)

#check { x := 1 : C } -- works
#check { y := 1 : C } -- doesn't work, should be { y := 1, z := 2*1, x := 2*1 + 3 }
#check { z := 1 : C } -- doesn't work, should be { z := 1, x := 1 + 3, y := (1 + 3) + 1 }
#check { z := 1, x := 2 : C } -- works
#check { y := 1 : B } -- works, but reduced a `Add.add` into `Nat.add`

end Ex4
