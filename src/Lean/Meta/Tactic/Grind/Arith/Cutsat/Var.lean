/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.IntInstTesters
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat

namespace Lean.Meta.Grind.Arith.Cutsat

@[export lean_grind_cutsat_mk_var]
def mkVarImpl (expr : Expr) : GoalM Var := do
  if let some var := (← get').varMap.find? { expr } then
    return var
  let var : Var := (← get').vars.size
  trace[grind.debug.cutsat.internalize] "{expr} ↦ #{var}"
  modify' fun s => { s with
    vars      := s.vars.push expr
    varMap    := s.varMap.insert { expr } var
    dvds      := s.dvds.push none
    lowers    := s.lowers.push {}
    uppers    := s.uppers.push {}
    diseqs    := s.diseqs.push {}
    occurs    := s.occurs.push {}
    elimEqs   := s.elimEqs.push none
  }
  markAsCutsatTerm expr
  assertNatCast expr var
  assertDenoteAsIntNonneg expr
  return var

def isInt (e : Expr) : GoalM Bool := do
  isDefEq (← inferType e) (mkConst ``Int)

def isAdd? (e : Expr) (report := true) : GoalM (Option (Expr × Expr)) := do
  let_expr HAdd.hAdd _ _ _ inst a b ← e | return none
  unless (← isInstHAddInt inst) do
    if report then
      reportIssue! "found term with non-standard instance{indentExpr e}"
    return none
  return some (a, b)

def isAdd (e : Expr) : GoalM Bool := do
  return (← isAdd? e false).isSome

def isMul? (e : Expr) (report := true) : GoalM (Option (Int × Expr)) := do
  let_expr HMul.hMul _ _ _ inst a b ← e
    | return none
  unless (← isInstHMulInt inst) do
    if report then
      reportIssue! "found term with non-standard instance{indentExpr e}"
    return none
  let some k ← getIntValue? a
    | return none
  return some (k, b)

def isMul (e : Expr) : GoalM Bool := do
  return (← isMul? e false).isSome

def addMonomial (e : Expr) (p : Poly) : GoalM Poly := do
  if let some (k, x) ← isMul? e then
    return .add k (← mkVar x) p
  if let some k ← getIntValue? e then
    if p.isZero then
      return .num k
    else
      reportIssue! "monomial expected, found numeral{indentExpr e}\ninternalizing as variable"
  return .add 1 (← mkVar e) p

partial def toPoly (e : Expr) : GoalM Poly := do
  if let some (a, b) ← isAdd? e then
    go a (← addMonomial b (.num 0))
  else
    addMonomial e (.num 0)
where
  go (e : Expr) (p : Poly) : GoalM Poly := do
    if let some (a, b) ← isAdd? e then
      go a (← addMonomial b p)
    else
      addMonomial e p

end Lean.Meta.Grind.Arith.Cutsat
