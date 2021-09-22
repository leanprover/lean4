/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic

namespace Lean.Elab.WF
open Meta

private def getDomains (preDefs : Array PreDefinition) : Array Expr :=
  preDefs.map fun preDef => preDef.type.bindingDomain!

private def mkNewDomain (ds : Array Expr) : MetaM Expr := do
  let mut r := ds.back
  for d in ds.pop.reverse do
    r ← mkAppM ``PSum #[d, r]
  return r

private def getCodomainLevel (preDef : PreDefinition) : MetaM Level :=
  forallBoundedTelescope preDef.type (some 1) fun _ body => getLevel body

private def getCodomainsLevel (preDefs : Array PreDefinition) : MetaM Level := do
  let r ← getCodomainLevel preDefs[0]
  for preDef in preDefs[1:] do
    unless (← isLevelDefEq r (← getCodomainLevel preDef)) do
      throwError "invalid mutual definition, result types must be in the same universe level"
  return r

private partial def mkNewCoDomain (x : Expr) (preDefs : Array PreDefinition) : MetaM Expr := do
  let u ← getCodomainsLevel preDefs
  let rec go (x : Expr) (i : Nat) : MetaM Expr := do
    if i < preDefs.size - 1 then
      let xType ← whnfD (← inferType x)
      assert! xType.isAppOfArity ``PSum 2
      let xTypeArgs := xType.getAppArgs
      let casesOn := mkConst (mkCasesOnName ``PSum) (mkLevelSucc u :: xType.getAppFn.constLevels!)
      let casesOn := mkAppN casesOn xTypeArgs -- parameters
      let casesOn := mkApp casesOn (← mkLambdaFVars #[x] (mkSort u)) -- motive
      let casesOn := mkApp casesOn x -- major
      let minor1 ← withLocalDeclD (← mkFreshUserName `_x) xTypeArgs[0] fun x =>
        mkLambdaFVars #[x] (preDefs[i].type.bindingBody!.instantiate1 x)
      let minor2 ← withLocalDeclD (← mkFreshUserName `_x) xTypeArgs[1] fun x => do
        mkLambdaFVars #[x] (← go x (i+1))
      return mkApp2 casesOn minor1 minor2
    else
      return preDefs[i].type.bindingBody!.instantiate1 x
  go x 0

private partial def packValues (x : Expr) (codomain : Expr) (preDefs : Array PreDefinition) : MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar codomain
  let rec go (mvarId : MVarId) (x : FVarId) (i : Nat) : MetaM Unit := do
    if i < preDefs.size - 1 then
      let #[s₁, s₂] ← cases mvarId x | unreachable!
      assignExprMVar s₁.mvarId (mkApp preDefs[i].value s₁.fields[0]).headBeta
      go s₂.mvarId s₂.fields[0].fvarId! (i+1)
    else
      assignExprMVar mvarId (mkApp preDefs[i].value (mkFVar x)).headBeta
  go mvar.mvarId! x.fvarId! 0
  instantiateMVars mvar

def packMutual (preDefs : Array PreDefinition) : MetaM PreDefinition := do
  if preDefs.size == 1 then return preDefs[0]
  withLocalDeclD (← mkFreshUserName `_x) (← mkNewDomain (getDomains preDefs)) fun x => do
    let codomain ← mkNewCoDomain x preDefs
    let type ← mkForallFVars #[x] codomain
    trace[Elab.definition.wf] "packMutual type: {type}"
    let value ← packValues x codomain preDefs
    trace[Elab.definition.wf] "packMutual value: {value}"
    let preDefNew := { preDefs[0] with declName := preDefs[0].declName ++ `_mutual, type, value }
    addAsAxiom preDefNew
    -- TODO: replace recursive applications
    return preDefNew

end Lean.Elab.WF
