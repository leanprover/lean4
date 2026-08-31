universe u

macro "Type*" : term => `(Type _)

open Nat

variable {α : Type u}

def vec : Type u → Nat → Type*
| A, 0      => PUnit
| A, succ k => A × vec A k

inductive dfin : Nat → Type
  | fz {n} : dfin (succ n)
  | fs {n} : dfin n → dfin (succ n)

def kth_projn : (n : Nat) → vec α n → dfin n → α
  | succ n, x,        dfin.fz   => x.fst
  | succ n, (x, xs),  dfin.fs k => kth_projn n xs k
