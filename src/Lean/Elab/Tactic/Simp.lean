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

def simpTarget (config : Meta.Simp.Config) (simpLemmas : SimpLemmas) : TacticM Unit := do
  let (g, gs) ← getMainGoal
  withMVarContext g do
    let target ← instantiateMVars (← getMVarDecl g).type
    let r ← simp target config simpLemmas
    match r.proof? with
    | some proof => setGoals ((← replaceTargetEq g r.expr proof) :: gs)
    | none => setGoals ((← replaceTargetDefEq g r.expr) :: gs)

-- TODO: improve simpLocalDecl and simpAll
-- TODO: issues: self simplification

def simpLocalDeclFVarId (config : Meta.Simp.Config) (simpLemmas : SimpLemmas) (fvarId : FVarId) : TacticM Unit := do
  let (g, gs) ← getMainGoal
  withMVarContext g do
    let localDecl ← getLocalDecl fvarId
    let r ← simp localDecl.type config simpLemmas
    match r.proof? with
    | some proof =>
      setGoals ((← replaceLocalDecl g fvarId r.expr proof).mvarId :: gs)
    | none => setGoals ((← changeLocalDecl g fvarId r.expr (checkDefEq := false)) :: gs)

def simpLocalDecl (config : Meta.Simp.Config) (simpLemmas : SimpLemmas) (userName : Name) : TacticM Unit :=
  withMainMVarContext do
    let localDecl ← getLocalDeclFromUserName userName
    simpLocalDeclFVarId config simpLemmas localDecl.fvarId

def simpAll (config : Meta.Simp.Config) (simpLemmas : SimpLemmas) : TacticM Unit := do
  let worked ← «try» (simpTarget config simpLemmas)
  withMainMVarContext do
    let mut worked := worked
    -- We must traverse backwards because `replaceLocalDecl` uses the revert/intro idiom
    for fvarId in (← getLCtx).getFVarIds.reverse do
      worked := worked || (← «try» <| simpLocalDeclFVarId config simpLemmas fvarId)
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

@[builtinTactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx => do
  let lemmas ← mkSimpLemmas stx[1]
  let config ← elabSimpConfig stx[2]
  let loc := expandOptLocation stx[3]
  match loc with
  | Location.target => simpTarget config lemmas
  | Location.localDecls userNames => userNames.forM (simpLocalDecl config lemmas)
  | Location.wildcard => simpAll config lemmas
  tryExactTrivial
where
  mkSimpLemmas (stx : Syntax) := do
    let lemmas ← getSimpLemmas
    if stx.isNone then
      return lemmas
    else
      /-
      syntax simpPre := "↓"
      syntax simpPost := "↑"
      syntax simpLemma := (simpPre <|> simpPost)? term
       -/
      let (g, _) ← getMainGoal
      withMVarContext g do
        let mut lemmas := lemmas
        for simpLemma in stx[1].getSepArgs do
          let post :=
            if simpLemma[0].isNone then
              true
            else
              simpLemma[0][0].getKind == ``Parser.Tactic.simpPost
          let term ← elabTerm simpLemma[1] none true
          lemmas ← lemmas.add term post
        return lemmas

end Lean.Elab.Tactic
