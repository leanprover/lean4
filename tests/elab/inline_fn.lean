

def f {α : Type} [Add α] (x : α) :=
x + x + x

partial def h : Nat → Nat
| 0     => 10
| n+1   => n * h n

def g1 (x : Nat) :=
inline f x

def g2 (x : Nat) :=
inline h x

def g3 :=
inline h 2
