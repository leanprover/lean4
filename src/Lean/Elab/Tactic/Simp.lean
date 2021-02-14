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

def simpTarget (ctx : Simp.Context) : TacticM Unit := do
  let (g, gs) ← getMainGoal
  withMVarContext g do
    let target ← instantiateMVars (← getMVarDecl g).type
    let r ← simp target ctx
    match r.proof? with
    | some proof => setGoals ((← replaceTargetEq g r.expr proof) :: gs)
    | none => setGoals ((← replaceTargetDefEq g r.expr) :: gs)

-- TODO: improve simpLocalDecl and simpAll
-- TODO: issues: self simplification
-- TODO: add new assertion with simplified result and clear old ones after simplifying all locals

def simpLocalDeclFVarId (ctx : Simp.Context) (fvarId : FVarId) : TacticM Unit := do
  let (g, gs) ← getMainGoal
  withMVarContext g do
    let localDecl ← getLocalDecl fvarId
    let r ← simp localDecl.type ctx
    match r.proof? with
    | some proof =>
      setGoals ((← replaceLocalDecl g fvarId r.expr proof).mvarId :: gs)
    | none => setGoals ((← changeLocalDecl g fvarId r.expr (checkDefEq := false)) :: gs)

def simpLocalDecl (ctx : Simp.Context) (userName : Name) : TacticM Unit :=
  withMainMVarContext do
    let localDecl ← getLocalDeclFromUserName userName
    simpLocalDeclFVarId ctx localDecl.fvarId

def simpAll (ctx : Simp.Context) : TacticM Unit := do
  let worked ← «try» (simpTarget ctx)
  withMainMVarContext do
    let mut worked := worked
    -- We must traverse backwards because `replaceLocalDecl` uses the revert/intro idiom
    for fvarId in (← getLCtx).getFVarIds.reverse do
      worked := worked || (← «try» <| simpLocalDeclFVarId ctx fvarId)
    unless worked do
      let (mvarId, _) ← getMainGoal
      throwTacticEx `simp mvarId "failed to simplify"

def tryExactTrivial : TacticM Unit := do
  let (g, gs) ← getMainGoal
  let gType ← getMVarType g
  if gType.isConstOf ``True then
    assignExprMVar g (mkConst ``True.intro)
    setGoals gs
  else
    pure ()

unsafe def evalSimpConfigUnsafe (e : Expr) : TermElabM Meta.Simp.Config :=
  Term.evalExpr Meta.Simp.Config ``Meta.Simp.Config e

@[implementedBy evalSimpConfigUnsafe] constant evalSimpConfig (e : Expr) : TermElabM Meta.Simp.Config

def elabSimpConfig (optConfig : Syntax) : TermElabM Meta.Simp.Config := do
  if optConfig.isNone then
    return {}
  else
    withLCtx {} {} <| withNewMCtxDepth <| Term.withSynthesize do
      let c ← Term.elabTermEnsuringType optConfig[0] (Lean.mkConst ``Meta.Simp.Config)
      evalSimpConfig (← instantiateMVars c)

/-- Return `some c`, if `e` is of the form `c.{?u_1, ..., ?u_n} ?m_1 ... ?m_k` -/
private def isGlobalLemma? (e : Expr) : Option Name :=
  e.withApp fun f args =>
    if f.isConst && args.all (·.isMVar) && f.constLevels!.all (·.isMVar) then
      some f.constName!
    else
      none

/-- Elaborate extra simp lemmas provided to `simp`. `stx` is of the `simpLemma,*` -/
private def elabSimpLemmas (stx : Syntax) (ctx : Simp.Context) : TacticM Simp.Context := do
  if stx.isNone then
    return ctx
  else
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? term
     -/
    let (g, _) ← getMainGoal
    withMVarContext g do
      let mut lemmas := ctx.simpLemmas
      for simpLemma in stx[1].getSepArgs do
        let post :=
          if simpLemma[0].isNone then
            true
          else
            simpLemma[0][0].getKind == ``Parser.Tactic.simpPost
        let lemma ← elabTerm simpLemma[1] none (mayPostpone := false)
        match isGlobalLemma? lemma with
        | some declName => lemmas ← lemmas.addConst declName post
        | none          => lemmas ← lemmas.add lemma post
      return { ctx with simpLemmas := lemmas }

@[builtinTactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx => do
  let ctx ← elabSimpLemmas stx[1] { config := (← elabSimpConfig stx[2]), simpLemmas := (← getSimpLemmas), congrLemmas := (← getCongrLemmas) }
  let loc := expandOptLocation stx[3]
  match loc with
  | Location.target => simpTarget ctx
  | Location.localDecls userNames => userNames.forM (simpLocalDecl ctx)
  | Location.wildcard => simpAll ctx
  tryExactTrivial

end Lean.Elab.Tactic
