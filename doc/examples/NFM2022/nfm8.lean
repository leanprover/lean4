/- Well-founded recursion -/

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by ack x y => (x, y)

def sum (a : Array Int) : Int :=
  let rec go (i : Nat) :=
     if i < a.size then
        a[i] + go (i+1)
     else
        0
  go 0
termination_by go i => a.size - i

set_option pp.proofs true
#print sum.go
/-
def sum.go : Array Int → Nat → Int :=
fun a =>
  WellFounded.fix (sum.go.proof_1 a) fun i a_1 =>
    if h : i < Array.size a then Array.getOp a i + a_1 (i + 1) (sum.go.proof_2 a i h) else 0
-/
