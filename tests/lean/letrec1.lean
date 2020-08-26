new_frontend

def f1.g := 10

def f1 (x : Nat) : Nat :=
letrec g : Nat → Nat -- Error f1.g has already been declared
  | 0   => x
  | y+1 => 2 * g y;
g (g x)

axiom Ax {α} : α

def f2 (x : Nat) : Nat :=
letrec
  g : Nat → Nat
  | 0   => 1
  | y+1 => (h y).val,
  h : (x : Nat) → { y : Nat // y < g x } -- unknown identifier `g`
  | 0 => ⟨10, Ax⟩
  | _ => ⟨20, Ax⟩;
10
