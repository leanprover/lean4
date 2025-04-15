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

def f4 (x : Nat × Nat) : Nat :=
let (a, b) := x;
a + b

#eval f4 (10, 20)

def f5 (x y : Nat) : Nat :=
let h : Nat → Nat → Nat
  | 0, b => b
  | a, b => a*b;
h x y

#eval f5 0 10
#eval f5 20 10

def f6 (x : Nat × Nat) : Nat :=
match x with
| { fst := x, .. } => x * 10

#eval f6 (5, 20)

def Vector' (α : Type) (n : Nat) := { a : Array α // a.size = n }

def mkVec {α : Type} (n : Nat) (a : α) : Vector' α n :=
⟨mkArray n a, Array.size_mkArray ..⟩

structure S :=
(n : Nat)
(y : Vector' Nat n)
(z : Vector' Nat n)
(h : y = z)
(m : { v : Nat // v = y.val.size })

def f7 (s : S) : Nat :=
match s with
| { n := n, m := m, .. } => n + m.val

#eval f7 { n := 10, y := mkVec 10 0, z := mkVec 10 0, h := rfl, m := ⟨10, rfl⟩ }

inductive Bla : Unit → Unit × Unit → Type where
  | left : Bla a (a, b)
  | right : Bla b (a, b)

def f8 : ∀ x y, Bla x y → Unit
  | _, _, .left => ()
  | _, _, .right => ()

example (x : Bla () ((), ())) : f8 () ((), ()) x = () := by simp only [f8]
