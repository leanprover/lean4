/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Meta.Tactic.Replace

namespace Lean.Elab.Tactic
open Meta

def finalizeSimpTarget (r : Simp.Result) : TacticM Bool := do
  if r.expr.isConstOf ``True then
    match r.proof? with
    | some proof => closeMainGoal (← mkOfEqTrue proof)
    | none => closeMainGoal (mkConst ``True.intro)
    return true
  else
    match r.proof? with
    | some proof => replaceMainGoal [← replaceTargetEq (← getMainGoal) r.expr proof]
    | none => replaceMainGoal [← replaceTargetDefEq (← getMainGoal) r.expr]
    return false

def simpTarget (ctx : Simp.Context) : TacticM Unit := do
  withMainContext do
    discard <| finalizeSimpTarget (← simp (← getMainTarget) ctx)

def finalizeSimpLocalDecl (fvarId : FVarId) (r : Simp.Result) : TacticM Bool := do
  if r.expr.isConstOf ``False then
    match r.proof? with
    | some proof => closeMainGoal (← mkFalseElim (← getMainTarget) (← mkEqMP proof (mkFVar fvarId)))
    | none => closeMainGoal (← mkFalseElim (← getMainTarget) (mkFVar fvarId))
    return true
  else
    match r.proof? with
    | some proof => replaceMainGoal [(← replaceLocalDecl (← getMainGoal) fvarId r.expr proof).mvarId]
    | none => replaceMainGoal [← changeLocalDecl (← getMainGoal) fvarId r.expr (checkDefEq := false)]
    return false

def simpLocalDeclFVarId (ctx : Simp.Context) (fvarId : FVarId) : TacticM Unit := do
  withMainContext do
    let localDecl ← getLocalDecl fvarId
    discard <| finalizeSimpLocalDecl fvarId (← simp localDecl.type ctx)

def simpLocalDecl (ctx : Simp.Context) (userName : Name) : TacticM Unit :=
  withMainContext do
    let localDecl ← getLocalDeclFromUserName userName
    simpLocalDeclFVarId ctx localDecl.fvarId

-- TODO: improve simpLocalDecl and simpAll
-- TODO: issues: self simplification
-- TODO: add new assertion with simplified result and clear old ones after simplifying all locals

def simpAll (ctx : Simp.Context) : TacticM Unit := do
  -- TODO: fix this
  let worked ← tryTactic (simpTarget ctx)
  withMainContext do
    let mut worked := worked
    -- We must traverse backwards because `replaceLocalDecl` uses the revert/intro idiom
    for fvarId in (← getLCtx).getFVarIds.reverse do
      worked := worked || (← tryTactic <| simpLocalDeclFVarId ctx fvarId)
    unless worked do
      throwTacticEx `simp (← getMainGoal) "failed to simplify"

unsafe def evalSimpConfigUnsafe (e : Expr) : TermElabM Meta.Simp.Config :=
  Term.evalExpr Meta.Simp.Config ``Meta.Simp.Config e

@[implementedBy evalSimpConfigUnsafe] constant evalSimpConfig (e : Expr) : TermElabM Meta.Simp.Config

/- `optConfig` is of the form `("(" "config" ":=" term ")")?` -/
def elabSimpConfig (optConfig : Syntax) : TermElabM Meta.Simp.Config := do
  if optConfig.isNone then
    return {}
  else
    withLCtx {} {} <| withNewMCtxDepth <| Term.withSynthesize do
      let c ← Term.elabTermEnsuringType optConfig[3] (Lean.mkConst ``Meta.Simp.Config)
      evalSimpConfig (← instantiateMVars c)

/-- Elaborate extra simp lemmas provided to `simp`. `stx` is of the `simpLemma,*` -/
private def elabSimpLemmas (stx : Syntax) (ctx : Simp.Context) : TacticM Simp.Context := do
  if stx.isNone then
    return ctx
  else
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? term

    syntax simpErase := "-" ident
    -/
    withMainContext do
      let mut lemmas := ctx.simpLemmas
      for arg in stx[1].getSepArgs do
        if arg.getKind == ``Lean.Parser.Tactic.simpErase then
          let declName ← resolveGlobalConstNoOverload arg[1].getId
          lemmas ← lemmas.erase declName
        else
          let post :=
            if arg[0].isNone then
              true
            else
              arg[0][0].getKind == ``Parser.Tactic.simpPost
          match (← resolveSimpIdLemma? arg[1]) with
          | some e =>
            if e.isConst then
              let declName := e.constName!
              let info ← getConstInfo declName
              if (← isProp info.type) then
                lemmas ← lemmas.addConst declName post
              else
                lemmas := lemmas.addDeclToUnfold declName
            else
              lemmas ← lemmas.add e post
          | _ =>
            let arg ← elabTerm arg[1] none (mayPostpone := false)
            lemmas ← lemmas.add arg post
      return { ctx with simpLemmas := lemmas }
where
  resolveSimpIdLemma? (simpArgTerm : Syntax) : TacticM (Option Expr) := do
    if simpArgTerm.isIdent then
      try
        Term.resolveId? simpArgTerm
      catch _ =>
        return none
    else
      return none

/-
  "simp " ("(" "config" ":=" term ")")? ("only ")? ("[" simpLemma,* "]")? (location)?
-/
@[builtinTactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx => do
  let simpOnly := !stx[2].isNone
  let ctx  ← elabSimpLemmas stx[3] {
    config      := (← elabSimpConfig stx[1])
    simpLemmas  := if simpOnly then {} else (← getSimpLemmas)
    congrLemmas := (← getCongrLemmas)
  }
  let loc := expandOptLocation stx[4]
  match loc with
  | Location.target => simpTarget ctx
  | Location.localDecls userNames => userNames.forM (simpLocalDecl ctx)
  | Location.wildcard => simpAll ctx

end Lean.Elab.Tactic
