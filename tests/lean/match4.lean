new_frontend

def f1 (x : Nat × Nat) : Nat :=
match x with
| { fst := x, snd := y } => x - y

#eval f1 (20, 15)

def g1 (h : Nat × Nat × Nat → Nat) : Nat :=
h (1, 2, 3)

def f2 (w : Nat) : Nat :=
g1 fun (x, y, z) => x + y + z + w

#eval f2 10

def g2 (h : Nat × Nat → Nat × Nat → Nat) : Nat :=
h (1, 2) (20, 40)

def f3 (a : Nat) : Nat :=
g2 fun (x, y) (z, w) => a*(y - x) + (w - z)

#eval f3 100

/-
set_option syntaxMaxDepth 1000
set_option trace.Elab true

def f4 (x : Nat) : Nat :=
let h : Nat → Nat → Nat
  | 0, b => b
  | a, b => a*b;
h x x
-/

/-
def f2 (x : Nat × Nat) : Nat :=
match x with
| { fst := x, .. } => x * 10
-/
