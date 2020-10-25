

namespace Ex1

structure A :=
(x : Nat)

structure B extends A :=
(y : Nat := x + 2) (x := y + 1)

structure C extends B :=
(z : Nat) (x := z + 10)

end Ex1

namespace Ex2

structure A :=
(x : Nat) (y : Nat)

structure B extends A :=
(z : Nat := x + 1) (y := z + x)

end Ex2

namespace Ex3

structure A :=
(x : Nat)

structure B extends A :=
(y : Nat := x + 2) (x := y + 1)

structure C extends B :=
(z : Nat := 2*y) (x := z + 2) (y := z + 3)

end Ex3

namespace Ex4

structure A :=
(x : Nat)

structure B extends A :=
(y : Nat := x + 1) (x := y + 1)

structure C extends B :=
(z : Nat := 2*y) (x := z + 3)

end Ex4

namespace Ex1

#check { y := 1 : B }
#check { z := 1 : C }

end Ex1

namespace Ex2

#check { x := 1 : B }

end Ex2

namespace Ex3

#check { x := 1 : C }
#check { y := 1 : C }
#check { z := 1 : C }

end Ex3

namespace Ex4

#check { x := 1 : C } -- works
#check { y := 1 : C } -- works
#check { z := 1 : C } -- works
#check { z := 1, x := 2 : C } -- works
#check { y := 1 : B } -- works

end Ex4
