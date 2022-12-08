structure FooS where
  x : Nat
  y : Nat
  h : x = y

structure BarS extends FooS where
  h' : x = y
  h  := h'

def f (x : Nat) : BarS :=
  { x,  y := x, h' := rfl }

def f1 (x : Nat) : BarS :=
  { x,  h' := rfl }
