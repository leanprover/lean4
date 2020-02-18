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

new_frontend

namespace Ex1

#check { B . y := 1 }
#check { C . z := 1 }

end Ex1

namespace Ex2

#check { B . x := 1 }

end Ex2

namespace Ex3

#check { C . x := 1 }
#check { C . y := 1 }
#check { C . z := 1 }

end Ex3

namespace Ex4

#check { C . x := 1 } -- works
#check { C . y := 1 } -- works
#check { C . z := 1 } -- works
#check { C . z := 1, x := 2 } -- works
#check { B . y := 1 } -- works

end Ex4
