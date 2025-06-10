structure FooS where
  x : Nat
  y : Nat
  h : x = y

structure BarS extends FooS where
  h' : x = y
  h  := h'

def f (x : Nat) : BarS :=
  { x,  y := x, h' := rfl }

/-- error: cannot synthesize placeholder for field 'h' -/
#guard_msgs in
example (x : Nat) : BarS :=
  { x, h' := rfl, .. }

def f1 (x : Nat) : BarS :=
  { x, h' := rfl, y := _ }
