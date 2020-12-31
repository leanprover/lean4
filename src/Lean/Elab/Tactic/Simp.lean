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

def simpTarget (simpLemmas : SimpLemmas) : TacticM Unit := do
  let (g, gs) ← getMainGoal
  withMVarContext g do
    let target ← instantiateMVars (← getMVarDecl g).type
    let r ← simp target simpLemmas
    match r.proof? with
    | some proof => setGoals ((← replaceTargetEq g r.expr proof) :: gs)
    | none => setGoals ((← replaceTargetDefEq g r.expr) :: gs)

def simpLocalDeclFVarId (simpLemmas : SimpLemmas) (fvarId : FVarId) : TacticM Unit := do
  let (g, gs) ← getMainGoal
  withMVarContext g do
    let localDecl ← getLocalDecl fvarId
    let r ← simp localDecl.type simpLemmas
    match r.proof? with
    | some proof => setGoals ((← replaceLocalDecl g fvarId r.expr proof).mvarId :: gs)
    | none => setGoals ((← changeLocalDecl g fvarId r.expr (checkDefEq := false)) :: gs)

def simpLocalDecl (simpLemmas : SimpLemmas) (userName : Name) : TacticM Unit :=
  withMainMVarContext do
    let localDecl ← getLocalDeclFromUserName userName
    simpLocalDeclFVarId simpLemmas localDecl.fvarId

def simpAll (simpLemmas : SimpLemmas) : TacticM Unit := do
  let worked ← «try» (simpTarget simpLemmas)
  withMainMVarContext do
    let mut worked := worked
    -- We must traverse backwards because `replaceLocalDecl` uses the revert/intro idiom
    for fvarId in (← getLCtx).getFVarIds.reverse do
      worked := worked || (← «try» <| simpLocalDeclFVarId simpLemmas fvarId)
    unless worked do
      let (mvarId, _) ← getMainGoal
      throwTacticEx `simp mvarId "failed to simplify"

@[builtinTactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx => do
  let lemmas ← mkSimpLemmas stx[1]
  let loc  := expandOptLocation stx[2]
  match loc with
  | Location.target => simpTarget lemmas
  | Location.localDecls userNames => userNames.forM (simpLocalDecl lemmas)
  | Location.wildcard => simpAll lemmas
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
        for simpLemma in stx[1].getArgs do
          let post :=
            if simpLemma[0].isNone then
              true
            else
              simpLemma[0][0].getKind == ``Parser.Tactic.simpPost
          let term ← elabTerm simpLemma[1] none true
          lemmas ← lemmas.add term post
        return lemmas

end Lean.Elab.Tactic
