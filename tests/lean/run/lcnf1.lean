import Lean

open Lean

run_meta Compiler.compile #[``List.map]

run_meta Compiler.compile #[``Lean.Elab.Term.synthesizeInstMVarCore]

run_meta Compiler.compile #[``Eq.ndrec]

def g1 (x : Nat) (h : Nat = Int) : Int :=
  (h ▸ x) + 1

run_meta Compiler.compile #[``g1]

def f (h : False) (x : Nat) : Nat :=
  (h.rec : Nat → Nat) x

run_meta Compiler.compile #[``f]

def g (as : Array (Nat → Nat)) (h : i < as.size ∧ q) : Nat :=
  h.casesOn (fun _ _ => as[i]) i

run_meta Compiler.compile #[``g]

def f2 {r : Nat → Nat → Prop} (q : Quot r) : Nat :=
  (q.lift (·+·) sorry : Nat → Nat) 2

run_meta Compiler.compile #[``f2]

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def Vec.zip : Vec α n → Vec β n → Vec (α × β) n
  | .cons a as, .cons b bs => .cons (a, b) (zip as bs)
  | .nil, .nil => .nil

def Vec.head : Vec α (n+1) → α
  | .cons a _ => a

run_meta Compiler.compile #[``Lean.Elab.Term.reportStuckSyntheticMVar]

run_meta Compiler.compile #[``Lean.Elab.Term.synthesizeSyntheticMVars]

set_option profiler true
run_meta Compiler.compile #[``Lean.Meta.isExprDefEqAuxImpl]

def foo (a b : Nat) :=
  let d := match a with
  | .zero => b
  | .succ c => c
  let e := match b with
  | .zero => a
  | .succ f => f
  Nat.add d e

run_meta Compiler.compile #[``foo]

run_meta Compiler.compile #[``Vec.zip]


structure Foo where
  α : Sort u
  x : α

def foo1 :=  Foo.mk Type Nat

run_meta Compiler.compile #[``foo1]

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

run_meta Compiler.compile #[``mkConstTuple]
run_meta Compiler.compile #[``Tuple.map]
run_meta Compiler.compile #[``Tuple.example]

def gebner1 (x : UInt64) : UInt64 := assert! x > 0; x - 1
-- set_option pp.letVarTypes true in
run_meta Compiler.compile #[``gebner1]

def gebner2 (x : UInt64) := x &&& ((1 : UInt64) <<< 5 : UInt64)
-- set_option pp.letVarTypes true in
run_meta Compiler.compile #[``gebner2]

run_meta Compiler.compile #[``Lean.Meta.instMonadMetaM]
run_meta Compiler.compile #[``Lean.Core.instMonadCoreM]
run_meta Compiler.compile #[``instMonadEIO]
-- set_option pp.explicit true in
run_meta Compiler.compile #[``EStateM.instMonad]
