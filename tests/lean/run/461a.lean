structure FooS where
  x : Nat
  y : Nat
  h : x = y := by rfl

/-- info: constructor FooS.mk : (x y : Nat) → autoParam (x = y) FooS.h._autoParam → FooS -/
#guard_msgs in
#print FooS.mk

def f1 (x : Nat) : FooS :=
  { x := x, y := x }

structure BooS where
  x : Nat
  y : Nat
  h (aux1 : True) (aux2 : x > 2) : x = y := by { intros; rfl }

/--
info: constructor BooS.mk : (x y : Nat) → autoParam (True → x > 2 → x = y) BooS.h._autoParam → BooS
-/
#guard_msgs in
#print BooS.mk

def f2 (x : Nat) : BooS :=
  { x := x, y := x }
