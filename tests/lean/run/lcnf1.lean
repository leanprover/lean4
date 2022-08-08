import Lean

open Lean
set_option trace.Meta.debug true
set_option pp.proofs true

-- set_option pp.match false
#eval Compiler.compile #[``List.map]

#eval Compiler.compile #[``Lean.Elab.Term.synthesizeInstMVarCore]
#check @Eq.rec

#eval Compiler.compile #[``Eq.ndrec]

def f (h : False) (x : Nat) : Nat :=
  (h.rec : Nat → Nat) x

#check @False.casesOn

#eval Compiler.compile #[``f]

def g (as : Array (Nat → Nat)) (h : i < as.size ∧ q) : Nat :=
  h.casesOn (fun _ _ => as[i]) i

set_option pp.notation false in
#eval Compiler.compile #[``g]

def f2 {r : Nat → Nat → Prop} (q : Quot r) : Nat :=
  (q.lift (·+·) sorry : Nat → Nat) 2

#print Quot.lift
#eval Compiler.compile #[``f2]

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def Vec.zip : Vec α n → Vec β n → Vec (α × β) n
  | .cons a as, .cons b bs => .cons (a, b) (zip as bs)
  | .nil, .nil => .nil

def Vec.head : Vec α (n+1) → α
  | .cons a _ => a

#eval Compiler.compile #[``Vec.zip]

#eval Compiler.compile #[``Vec.zip.match_1]
