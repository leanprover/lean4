def f {α : Type} [HasAdd α] (x : α) :=
x + x + x

def h : Nat → Nat
| 0     := 10
| (n+1) := n * h n

setOption pp.all True
setOption Trace.Compiler True

def g1 (x : Nat) :=
inline f x

def g2 (x : Nat) :=
inline h x

def g3 :=
inline h 2
