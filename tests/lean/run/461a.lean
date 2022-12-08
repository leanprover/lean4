structure FooS where
  x : Nat
  y : Nat
  h : x = y := by rfl

#print FooS.mk

def f1 (x : Nat) : FooS :=
  { x := x, y := x }

structure BooS where
  x : Nat
  y : Nat
  h (aux1 : True) (aux2 : x > 2) : x = y := by { intros; rfl }

#print BooS.mk

def f2 (x : Nat) : BooS :=
  { x := x, y := x }
