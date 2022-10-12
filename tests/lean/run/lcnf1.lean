import Lean

open Lean

#eval Compiler.compile #[``List.map]

#eval Compiler.compile #[``Lean.Elab.Term.synthesizeInstMVarCore]

#eval Compiler.compile #[``Eq.ndrec]

def g1 (x : Nat) (h : Nat = Int) : Int :=
  (h ▸ x) + 1

#eval Compiler.compile #[``g1]

def f (h : False) (x : Nat) : Nat :=
  (h.rec : Nat → Nat) x

#eval Compiler.compile #[``f]

def g (as : Array (Nat → Nat)) (h : i < as.size ∧ q) : Nat :=
  h.casesOn (fun _ _ => as[i]) i

#eval Compiler.compile #[``g]

def f2 {r : Nat → Nat → Prop} (q : Quot r) : Nat :=
  (q.lift (·+·) sorry : Nat → Nat) 2

#eval Compiler.compile #[``f2]

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def Vec.zip : Vec α n → Vec β n → Vec (α × β) n
  | .cons a as, .cons b bs => .cons (a, b) (zip as bs)
  | .nil, .nil => .nil

def Vec.head : Vec α (n+1) → α
  | .cons a _ => a

#eval Compiler.compile #[``Lean.Elab.Term.reportStuckSyntheticMVar]

#eval Compiler.compile #[``Lean.Elab.Term.synthesizeSyntheticMVars]

set_option profiler true
#eval Compiler.compile #[``Lean.Meta.isExprDefEqAuxImpl]

def foo (a b : Nat) :=
  let d := match a with
  | .zero => b
  | .succ c => c
  let e := match b with
  | .zero => a
  | .succ f => f
  Nat.add d e

#eval Compiler.compile #[``foo]

#eval Compiler.compile #[``Vec.zip]


structure Foo where
  α : Sort u
  x : α

def foo1 :=  Foo.mk Type Nat

#eval Compiler.compile #[``foo1]

def Tuple (α : Type u) : Nat → Type u
  | 0   => PUnit
  | 1   => α
  | n+2 => α × Tuple α (n+1)

def mkConstTuple (a : α) : (n : Nat) → Tuple α n
  | 0 => ⟨⟩
  | 1 => a
  | n+2 => (a, mkConstTuple a (n+1))

def Tuple.map (f : α → β) (xs : Tuple α n) : Tuple β n :=
  match n with
  | 0 => ⟨⟩
  | 1 => f xs
  | _+2 => match xs with
    | (a, xs) => (f a, Tuple.map f xs)

def Tuple.example (a b : Nat) :=
  Tuple.map (n := 2) (· + 1) (a, b)

#eval Compiler.compile #[``mkConstTuple]
#eval Compiler.compile #[``Tuple.map]
#eval Compiler.compile #[``Tuple.example]

def gebner1 (x : UInt64) : UInt64 := assert! x > 0; x - 1
-- set_option pp.letVarTypes true in
#eval Compiler.compile #[``gebner1]

def gebner2 (x : UInt64) := x &&& ((1 : UInt64) <<< 5 : UInt64)
-- set_option pp.letVarTypes true in
#eval Compiler.compile #[``gebner2]

#eval Compiler.compile #[``Lean.Meta.instMonadMetaM]
#eval Compiler.compile #[``Lean.Core.instMonadCoreM]
#eval Compiler.compile #[``instMonadEIO]
-- set_option pp.explicit true in
#eval Compiler.compile #[``EStateM.instMonadEStateM]
