/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp
import Lean.Meta.Tactic.Replace
import Lean.Elab.BuiltinNotation
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config

namespace Lean.Elab.Tactic
open Meta

declare_config_elab elabSimpConfigCore    Meta.Simp.Config
declare_config_elab elabSimpConfigCtxCore Meta.Simp.ConfigCtx

/-
  `optConfig` is of the form `("(" "config" ":=" term ")")?`
  If `ctx == false`, the argument is assumed to have type `Meta.Simp.Config`, and `Meta.Simp.ConfigCtx` otherwise. -/
def elabSimpConfig (optConfig : Syntax) (ctx : Bool) : TermElabM Meta.Simp.Config := do
  if ctx then
    return (← elabSimpConfigCtxCore optConfig).toConfig
  else
    elabSimpConfigCore optConfig

private def addDeclToUnfoldOrLemma (lemmas : Meta.SimpLemmas) (e : Expr) (post : Bool) (inv : Bool) : MetaM Meta.SimpLemmas := do
  if e.isConst then
    let declName := e.constName!
    let info ← getConstInfo declName
    if (← isProp info.type) then
      lemmas.addConst declName (post := post) (inv := inv)
    else
      if inv then
        throwError "invalid '←' modifier, '{declName}' is a declaration name to be unfolded"
      lemmas.addDeclToUnfold declName
  else
    lemmas.add #[] e (post := post) (inv := inv)

private def addSimpLemma (lemmas : Meta.SimpLemmas) (stx : Syntax) (post : Bool) (inv : Bool) : TermElabM Meta.SimpLemmas := do
  let (levelParams, proof) ← Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return (r.paramNames, r.expr)
    else
      return (#[], e)
  lemmas.add levelParams proof (post := post) (inv := inv)

structure ElabSimpArgsResult where
  ctx     : Simp.Context
  starArg : Bool := false

/--
  Elaborate extra simp lemmas provided to `simp`. `stx` is of the `simpLemma,*`
  If `eraseLocal == true`, then we consider local declarations when resolving names for erased lemmas (`- id`),
  this option only makes sense for `simp_all`.
-/
private def elabSimpArgs (stx : Syntax) (ctx : Simp.Context) (eraseLocal : Bool) : TacticM ElabSimpArgsResult := do
  if stx.isNone then
    return { ctx }
  else
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? term

    syntax simpErase := "-" ident
    -/
    withMainContext do
      let mut lemmas  := ctx.simpLemmas
      let mut starArg := false
      for arg in stx[1].getSepArgs do
        if arg.getKind == ``Lean.Parser.Tactic.simpErase then
          if eraseLocal && (← Term.isLocalIdent? arg[1]).isSome then
            -- We use `eraseCore` because the simp lemma for the hypothesis was not added yet
            lemmas ← lemmas.eraseCore arg[1].getId
          else
            let declName ← resolveGlobalConstNoOverloadWithInfo arg[1]
            lemmas ← lemmas.erase declName
        else if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
          let post :=
            if arg[0].isNone then
              true
            else
              arg[0][0].getKind == ``Parser.Tactic.simpPost
          let inv  := !arg[1].isNone
          let term := arg[2]
          match (← resolveSimpIdLemma? term) with
          | some e => lemmas ← addDeclToUnfoldOrLemma lemmas e post inv
          | _      => lemmas ← addSimpLemma lemmas term post inv
        else if arg.getKind == ``Lean.Parser.Tactic.simpStar then
          starArg := true
        else
          throwUnsupportedSyntax
      return { ctx := { ctx with simpLemmas := lemmas }, starArg }
where
  resolveSimpIdLemma? (simpArgTerm : Syntax) : TacticM (Option Expr) := do
    if simpArgTerm.isIdent then
      try
        Term.resolveId? simpArgTerm (withInfo := true)
      catch _ =>
        return none
    else
      Term.elabCDotFunctionAlias? simpArgTerm

abbrev FVarIdToLemmaId := FVarIdMap Name

-- TODO: move?
private def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isAuxDecl do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result

structure MkSimpContextResult where
  ctx             : Simp.Context
  fvarIdToLemmaId : FVarIdToLemmaId

--  If `ctx == false`, the argument is assumed to have type `Meta.Simp.Config`, and `Meta.Simp.ConfigCtx` otherwise. -/
def mkSimpContext (stx : Syntax) (eraseLocal : Bool) (ctx := false) (ignoreStarArg : Bool := false) : TacticM MkSimpContextResult := do
  let simpOnly := !stx[2].isNone
  let simpLemmas ←
    if simpOnly then
      ({} : SimpLemmas).addConst ``eq_self
    else
      getSimpLemmas
  let congrLemmas ← getCongrLemmas
  let r ← elabSimpArgs stx[3] (eraseLocal := eraseLocal) {
    config      := (← elabSimpConfig stx[1] (ctx := ctx))
    simpLemmas, congrLemmas
  }
  if !r.starArg || ignoreStarArg then
    return { r with fvarIdToLemmaId := {} }
  else
    let ctx := r.ctx
    let erased := ctx.simpLemmas.erased
    let hs ← getPropHyps
    let mut ctx := ctx
    let mut fvarIdToLemmaId := {}
    for h in hs do
      let localDecl ← getLocalDecl h
      unless erased.contains localDecl.userName do
        let fvarId := localDecl.fvarId
        let proof  := localDecl.toExpr
        let id     ← mkFreshUserName `h
        fvarIdToLemmaId := fvarIdToLemmaId.insert fvarId id
        let simpLemmas ← ctx.simpLemmas.add #[] proof (name? := id)
        ctx := { ctx with simpLemmas }
    return { ctx, fvarIdToLemmaId }

/-
  "simp " ("(" "config" ":=" term ")")? ("only ")? ("[" simpLemma,* "]")? (location)?
-/
@[builtinTactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx => do
  let { ctx, fvarIdToLemmaId } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  -- trace[Meta.debug] "Lemmas {← toMessageData ctx.simpLemmas.post}"
  let loc := expandOptLocation stx[4]
  match loc with
  | Location.targets hUserNames simplifyTarget =>
    withMainContext do
      let fvarIds ← hUserNames.mapM fun hUserName => return (← getLocalDeclFromUserName hUserName).fvarId
      go ctx fvarIds simplifyTarget fvarIdToLemmaId
  | Location.wildcard =>
    withMainContext do
      go ctx (← getNondepPropHyps (← getMainGoal)) (simplifyTarget := true) fvarIdToLemmaId
where
  go (ctx : Simp.Context) (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) (fvarIdToLemmaId : FVarIdToLemmaId) : TacticM Unit := do
    liftMetaTactic1 fun mvarId =>
      return (← simpGoal mvarId ctx (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIdsToSimp) (fvarIdToLemmaId := fvarIdToLemmaId)).map (·.2)

@[builtinTactic Lean.Parser.Tactic.simpAll] def evalSimpAll : Tactic := fun stx => do
  let { ctx, .. } ← mkSimpContext stx (eraseLocal := true) (ctx := true) (ignoreStarArg := true)
  match (← simpAll (← getMainGoal) ctx) with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [mvarId]

end Lean.Elab.Tactic
