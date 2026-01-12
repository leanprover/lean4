/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt
public section
namespace Lean.Meta.Grind.Arith.Cutsat

@[extern "lean_cutsat_propagate_nonlinear"]
opaque propagateNonlinearTerm (y : Var) (x : Var) : GoalM Bool

/-
**Note**: It is safe to use (the more efficient) structural instances tests here because `grind` uses the canonicalizer.
-/
open Structural

private def isNonlinearTerm (e : Expr) : MetaM Bool := do
  match_expr e with
  | HMul.hMul _ _ _ i _ _ => isInstHMulInt i
  | HDiv.hDiv _ _ _ i _ b => pure (← getIntValue? b).isNone <&&> isInstHDivInt i
  | HMod.hMod _ _ _ i _ b => pure (← getIntValue? b).isNone <&&> isInstHModInt i
  | HPow.hPow _ _ _ i a b =>
    unless (← isInstHPowInt i) do return false
    return (← getIntValue? a).isNone || (← getIntValue? b).isNone
  | _ => return false

private def registerNonlinearOcc (arg : Expr) (x : Var) : GoalM Unit := do
  let y ← mkVar arg
  if (← get').elimEqs[y]!.isSome then
    if (← propagateNonlinearTerm y x) then
      return ()
  let occs := (← get').nonlinearOccs.find? y |>.getD []
  unless x ∈ occs do
  modify' fun s => { s with nonlinearOccs := s.nonlinearOccs.insert y (x::occs) }

private partial def registerNonlinearOccsAt (e : Expr) (x : Var) : GoalM Unit := do
  match_expr e with
  | HMul.hMul _ _ _ _ a b => go a; go b
  | HDiv.hDiv _ _ _ _ _ b => registerNonlinearOcc b x
  | HMod.hMod _ _ _ _ _ b => registerNonlinearOcc b x
  | HPow.hPow _ _ _ _ a b =>
    if (← getIntValue? a).isNone then
      registerNonlinearOcc a x
    if (← getIntValue? b).isNone && (← getNatValue? b).isNone then
      -- Recall that `b : Nat`, we must create `NatCast.natCast b` and watch it.
      let (b', _) ← mkNatVar b
      internalize b' (← getGeneration b)
      registerNonlinearOcc b' x
  | _ => return ()
where
  go (e : Expr) : GoalM Unit := do
    match_expr e with
    | HMul.hMul _ _ _ i a b =>
      if (← isInstHMulInt i) then
        go a; go b
      else
        registerNonlinearOcc e x
    | _ => registerNonlinearOcc e x

@[export lean_grind_cutsat_mk_var]
def mkVarImpl (expr : Expr) : GoalM Var := do
  if let some var := (← get').varMap.find? { expr } then
    return var
  let var : Var := (← get').vars.size
  trace[grind.debug.lia.internalize] "{expr} ↦ #{var}"
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
  cutsatExt.markTerm expr
  assertNatCast expr var
  assertNonneg expr var
  assertToIntBounds expr var
  if (← isNonlinearTerm expr) then
    registerNonlinearOccsAt expr var
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
