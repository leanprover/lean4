universes u v

-- set_option pp.binder_types false
set_option pp.implicit true
set_option trace.compiler.llnf true
set_option trace.compiler.boxed true

namespace x1

def f (x : bool) (y z : nat) : nat :=
match x with
| tt := y
| ff := z + y + y

end x1


namespace x2

def f (x : nat) : nat := x

end x2


namespace x3

def f (x y : nat) : nat := x

end x3

namespace x4
@[noinline] def h (x y : nat) : nat := x + y

def f1 (x y : nat) : nat :=
h x y

def f2 (x y : nat) : nat :=
h (h x y) (h y x)

def f3 (x y : nat) : nat :=
h (h x x) x

def f4 (x y : nat) : nat :=
h (h 1 0) x

def f5 (x y : nat) : nat :=
h (h 1 1) x

end x4

namespace x5

def my_map {α : Type u} {β : Type v} (f : α → β) : list α → list β
| []      := []
| (x::xs) := f x :: my_map xs

end x5

namespace x6

@[noinline] def act : state nat unit :=
modify (+1)

def f : state nat unit :=
act *> act

end x6

namespace x7

inductive S
| v1 | v2 | v3

def foo : S → S × S
| S.v1 := (S.v2, S.v1)
| S.v2 := (S.v3, S.v2)
| S.v3 := (S.v1, S.v2)

end x7

namespace x8

def f (x : nat) : list nat :=
x :: x :: []

end x8
