def f {α : Type} [has_add α] (x : α) :=
x + x + x

def h : nat → nat
| 0     := 10
| (n+1) := n * h n

set_option pp.all true
set_option trace.compiler true

def g1 (x : nat) :=
inline f x

def g2 (x : nat) :=
inline h x

def g3 :=
inline h 2
