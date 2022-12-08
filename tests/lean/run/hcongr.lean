import Lean

inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def Vec.map (f : α → β) : Vec α n → Vec β n
  | nil => nil
  | cons a as => cons (f a) (map f as)

open Lean
open Lean.Meta

def tstHCongr (f : Expr) : MetaM Unit := do
  let result ← mkHCongr f
  check result.proof
  IO.println (← ppExpr result.type)
  IO.println (← ppExpr result.proof)
  unless (← isDefEq result.type (← inferType result.proof)) do
    throwError "invalid proof"

#eval tstHCongr (mkConst ``Vec.map [levelZero, levelZero])

#eval tstHCongr (mkApp2 (mkConst ``Vec.map [levelZero, levelZero]) (mkConst ``Nat) (mkConst ``Nat))
