/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Meta.Tactic.SymEval.Types

namespace Lean.Meta
namespace SymEval

def cacheResult (e : Expr) (r : Result) : M Result := do
  let dischargeDepth := (← read).dischargeDepth
  modify fun s => { s with cache := s.cache.insert e { r with dischargeDepth } }
  return r

def evalLit (e : Expr) : M Result :=
  -- TODO
  return { expr := e }

partial def seval (e : Expr) : M Result := withIncRecDepth do
  checkSystem "eval"
  if (← isProof e) then
    return { expr := e }
  if let some result := (← get).cache.find? e then
    if result.dischargeDepth ≤ (← read).dischargeDepth then
      return result
  loop { expr := e }
where
  loop (r : Result) : M Result := do
    let cfg ← getConfig
    if (← get).numSteps > cfg.maxSteps then
      throwError "'seval' failed, maximum number of steps exceeded"
    else
      modify fun s => { s with numSteps := s.numSteps + 1 }
      let r ← Simp.mkEqTrans r (← step r.expr)
      cacheResult e r

  step (e : Expr) : M Result := do
    trace[Meta.Tactic.seval.visit] "{e}"
    match e with
    | .mdata _ e   => seval e
    | .proj ..     => evalProj e
    | .app ..      => evalApp e
    | .lam ..      => evalLambda e
    | .forallE ..  => evalForall e
    | .letE ..     => evalLet e
    | .const ..    => evalConst e
    | .bvar ..     => unreachable!
    | .sort ..     => return { expr := e }
    | .lit ..      => evalLit e
    | .mvar ..     => seval (← instantiateMVars e)
    | .fvar ..     => evalFVar e

  evalConst (e : Expr) : M Result := do
    -- TODO
    return { expr := e }

  evalFVar (e : Expr) : M Result := do
    -- TODO
    return { expr := e }

  evalLet (e : Expr) : M Result := do
    -- TODO
    return { expr := e }

  evalProj (e : Expr) : M Result := do
    -- TODO
    return { expr := e }

  evalLambda (e : Expr) : M Result := do
    -- TODO
    return { expr := e }

  evalForall (e : Expr) : M Result := do
    -- TODO
    return { expr := e }

  congrArgs (r : Result) (args : Array Expr) : M Result := do
    Simp.congrArgs seval pure r args

  /-- Try to use automatically generated congruence theorems. See `mkCongrSimp?`. -/
  tryAutoCongrTheorem? (e : Expr) : M (Option Result) := do
    Simp.tryAutoCongrTheorem? seval pure e

  congr (e : Expr) : M Result := do
    if let some result ← tryAutoCongrTheorem? e then
      return result
    else
      e.withApp fun f args => do
        congrArgs (← seval f) args

  evalApp (e : Expr) : M Result := do
    -- TODO
    congr e

def main (e : Expr) (ctx : Context): MetaM Result := do
  try
    withoutCatchingRuntimeEx do
      let (r, _) ← seval e ctx |>.run {}
      return r
  catch ex =>
    if ex.isRuntime then throwNestedTacticEx `seval ex else throw ex

end SymEval

def seval (e : Expr) (ctx : SymEval.Context) : MetaM SymEval.Result := do profileitM Exception "seval" (← getOptions) do
  SymEval.main e ctx

/-- See `sevalTarget`. This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def sevalTargetCore (mvarId : MVarId) (ctx : SymEval.Context) : MetaM (Option MVarId) := do
  let target ← instantiateMVars (← mvarId.getType)
  let r ← seval target ctx
  if r.expr.consumeMData.isConstOf ``True then
    match r.proof? with
    | some proof => mvarId.assign (← mkOfEqTrue proof)
    | none => mvarId.assign (mkConst ``True.intro)
    return none
  else
    applySimpResultToTarget mvarId target r

/--
  Symbolic evaluate the given goal target (aka type).
  Return `none` if the goal was closed. Return `some mvarId'` otherwise,
  where `mvarId'` is the new reduced goal.
-/
def sevalTarget (mvarId : MVarId) (ctx : SymEval.Context := {}) : MetaM (Option MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `seval
    sevalTargetCore mvarId ctx

end Lean.Meta
