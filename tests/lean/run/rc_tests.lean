
universe u v

-- set_option pp.binderTypes false
set_option pp.explicit true
set_option trace.compiler.llnf true
-- set_option trace.compiler.boxed true

namespace x1

def f (x : Bool) (y z : Nat) : Nat :=
match x with
| true => y
| false => z + y + y

end x1


namespace x2

def f (x : Nat) : Nat := x

end x2


namespace x3

def f (x y : Nat) : Nat := x

end x3

namespace x4
@[noinline] def h (x y : Nat) : Nat := x + y

def f1 (x y : Nat) : Nat :=
h x y

def f2 (x y : Nat) : Nat :=
h (h x y) (h y x)

def f3 (x y : Nat) : Nat :=
h (h x x) x

def f4 (x y : Nat) : Nat :=
h (h 1 0) x

def f5 (x y : Nat) : Nat :=
h (h 1 1) x

end x4

namespace x5

partial def myMap {α : Type u} {β : Type v} (f : α → β) : List α → List β
| []      => []
| x::xs   => f x :: myMap f xs

end x5

namespace x6

@[noinline] def act : StateM Nat Unit :=
modify (fun a => a + 1)

def f : StateM Nat Unit :=
act *> act

end x6

namespace x7

inductive S
| v1 | v2 | v3

def foo : S → S × S
| S.v1 => (S.v2, S.v1)
| S.v2 => (S.v3, S.v2)
| S.v3 => (S.v1, S.v2)

end x7

namespace x8

def f (x : Nat) : List Nat :=
x :: x :: []

end x8
