instance : Coe Nat Int :=
⟨fun n => Int.ofNat n⟩

def f (x : Nat) : List Int :=
[x]

new_frontend

def g1 (x : Nat) : List Int :=
[x, x]

def g2 (n : Nat) (i : Int) : Int :=
0 + n + i

def g3 (n : Nat) (i : Int) : Int :=
let x : Int := n+i;
x + x
