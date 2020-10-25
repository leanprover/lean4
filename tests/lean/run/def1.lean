

inductive BV : Nat → Type
| nil  : BV 0
| cons : (n : Nat) → (hd : Bool) → (tl : BV n) → BV (Nat.succ n)

open BV

def h : {n : Nat} → BV n.succ.succ → Bool
| _, cons (Nat.succ (Nat.succ m)) b v => b
| _, cons (Nat.succ Nat.zero) b v     => not b

theorem ex1 (m : Nat) (b : Bool) (v : BV m.succ.succ) : h (cons m.succ.succ b v) = b :=
rfl

theorem ex2 (m : Nat) (b : Bool) (v : BV 1) : h (cons 1 b v) = not b :=
rfl
