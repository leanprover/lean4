/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

namespace Lean.Meta.Grind.Arith.Cutsat

private def mkNextForeignVarFor (e : Expr) (t : ForeignType) : GoalM Var := do
  let vars := (← get').foreignVars.find? t |>.getD {}
  let x := vars.size
  modify' fun s => { s with foreignVars := s.foreignVars.insert t (vars.push e) }
  return x

def mkForeignVar (e : Expr) (t : ForeignType) : GoalM Var := do
  if let some (x, t') := (← get').foreignVarMap.find? { expr := e } then
    assert! t == t'
    return x
  let vars := (← get').foreignVars.find? t |>.getD {}
  let x := vars.size
  modify' fun s => { s with
    foreignVars := s.foreignVars.insert t (vars.push e)
    foreignVarMap := s.foreignVarMap.insert { expr := e} (x, t)
  }
  markAsCutsatTerm e
  return x

def foreignTerm? (e : Expr) : GoalM (Option ForeignType) := do
  return (·.2) <$> (← get').foreignVarMap.find? { expr := e }

def hasForeignVar (e : Expr) : GoalM Bool :=
  return (← get').foreignVarMap.contains { expr := e }

def foreignTermOrLit? (e : Expr) : GoalM (Option ForeignType) := do
  if isNatNum e then return some .nat
  foreignTerm? e

def getForeignVars (t : ForeignType) : GoalM (PArray Expr) := do
  return (← get').foreignVars.find? t |>.getD {}

protected def ForeignType.denoteType : ForeignType → Expr
  | .nat => mkConst ``Nat

end Lean.Meta.Grind.Arith.Cutsat
