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

/--
  Implement a `simp` discharge function using the given tactic syntax code.
  Recall that `simp` dischargers are in `SimpM` which does not have access to `Term.State`.
  We need access to `Term.State` to store messages and update the info tree.
  Thus, we create an `IO.ref` to track these changes at `Term.State` when we execute `tacticCode`.
  We must set this reference with the current `Term.State` before we execute `simp` using the
  generated `Simp.Discharge`. -/
def tacticToDischarge (tacticCode : Syntax) : TacticM (IO.Ref Term.State × Simp.Discharge) := do
  let tacticCode ← `(tactic| try ($tacticCode:tacticSeq))
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let disch : Simp.Discharge := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    let s ← ref.get
    let runTac? : TermElabM (Option Expr) :=
      try
        /- We must only save messages and info tree changes. Recall that `simp` uses temporary metavariables (`withNewMCtxDepth`).
           So, we must not save references to them at `Term.State`. -/
        withoutModifyingStateWithInfoAndMessages do
          Term.withSynthesize (mayPostpone := false) <| Term.runTactic mvar.mvarId! tacticCode
          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, s) ← liftM (m := MetaM) <| Term.TermElabM.run runTac? ctx s
    ref.set s
    return result?
  return (ref, disch)

inductive Simp.DischargeWrapper where
  | default
  | custom (ref : IO.Ref Term.State) (discharge : Simp.Discharge)

def Simp.DischargeWrapper.with (w : Simp.DischargeWrapper) (x : Option Simp.Discharge → TacticM α) : TacticM α := do
  match w with
  | default => x none
  | custom ref d =>
    ref.set (← getThe Term.State)
    try
      x d
    finally
      set (← ref.get)

private def mkDischargeWrapper (optDischargeSyntax : Syntax) : TacticM Simp.DischargeWrapper := do
  if optDischargeSyntax.isNone then
    return Simp.DischargeWrapper.default
  else
    let (ref, d) ← tacticToDischarge optDischargeSyntax[0][3]
    return Simp.DischargeWrapper.custom ref d

/-
  `optConfig` is of the form `("(" "config" ":=" term ")")?`
  If `ctx == false`, the argument is assumed to have type `Meta.Simp.Config`, and `Meta.Simp.ConfigCtx` otherwise. -/
def elabSimpConfig (optConfig : Syntax) (ctx : Bool) : TermElabM Meta.Simp.Config := do
  if ctx then
    return (← elabSimpConfigCtxCore optConfig).toConfig
  else
    elabSimpConfigCore optConfig

private def addDeclToUnfoldOrTheorem (thms : Meta.SimpTheorems) (e : Expr) (post : Bool) (inv : Bool) : MetaM Meta.SimpTheorems := do
  if e.isConst then
    let declName := e.constName!
    let info ← getConstInfo declName
    if (← isProp info.type) then
      thms.addConst declName (post := post) (inv := inv)
    else
      if inv then
        throwError "invalid '←' modifier, '{declName}' is a declaration name to be unfolded"
      thms.addDeclToUnfold declName
  else
    thms.add #[] e (post := post) (inv := inv)

private def addSimpTheorem (thms : Meta.SimpTheorems) (stx : Syntax) (post : Bool) (inv : Bool) : TermElabM Meta.SimpTheorems := do
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
  thms.add levelParams proof (post := post) (inv := inv)

structure ElabSimpArgsResult where
  ctx     : Simp.Context
  starArg : Bool := false

inductive ResolveSimpIdResult where
  | none
  | expr (e : Expr)
  | ext  (ext : SimpExtension)

/--
  Elaborate extra simp theorems provided to `simp`. `stx` is of the `simpTheorem,*`
  If `eraseLocal == true`, then we consider local declarations when resolving names for erased theorems (`- id`),
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
      let mut thmsArray := ctx.simpTheorems
      let mut thms      := thmsArray[0]
      let mut starArg   := false
      for arg in stx[1].getSepArgs do
        if arg.getKind == ``Lean.Parser.Tactic.simpErase then
          if eraseLocal && (← Term.isLocalIdent? arg[1]).isSome then
            -- We use `eraseCore` because the simp theorem for the hypothesis was not added yet
            thms := thms.eraseCore arg[1].getId
          else
            let declName ← resolveGlobalConstNoOverloadWithInfo arg[1]
            if ctx.config.autoUnfold then
              thms := thms.eraseCore declName
            else
              thms ← thms.erase declName
        else if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
          let post :=
            if arg[0].isNone then
              true
            else
              arg[0][0].getKind == ``Parser.Tactic.simpPost
          let inv  := !arg[1].isNone
          let term := arg[2]

          match (← resolveSimpIdTheorem? term) with
          | .expr e  => thms ← addDeclToUnfoldOrTheorem thms e post inv
          | .ext ext => thmsArray := thmsArray.push (← ext.getTheorems)
          | .none    => thms ← addSimpTheorem thms term post inv
        else if arg.getKind == ``Lean.Parser.Tactic.simpStar then
          starArg := true
        else
          throwUnsupportedSyntax
      return { ctx := { ctx with simpTheorems := thmsArray.set! 0 thms }, starArg }
where
  resolveSimpIdTheorem? (simpArgTerm : Syntax) : TacticM ResolveSimpIdResult := do
    let resolveExt (n : Name) : TacticM ResolveSimpIdResult := do
      if let some ext ← getSimpExtension? n then
        return .ext ext
      else
        return .none
    if simpArgTerm.isIdent then
      try
        if let some e ← Term.resolveId? simpArgTerm (withInfo := true) then
          return .expr e
        else
          resolveExt simpArgTerm.getId
      catch _ =>
        resolveExt simpArgTerm.getId
    else if let some e ← Term.elabCDotFunctionAlias? simpArgTerm then
      return .expr e
    else
      return .none

structure MkSimpContextResult where
  ctx              : Simp.Context
  dischargeWrapper : Simp.DischargeWrapper
  fvarIdToLemmaId  : FVarIdToLemmaId

/--
  If `ctx == false`, the config argument is assumed to have type `Meta.Simp.Config`, and `Meta.Simp.ConfigCtx` otherwise.
  If `ctx == false`, the `discharge` option must be none -/
def mkSimpContext (stx : Syntax) (eraseLocal : Bool) (ctx := false) (ignoreStarArg : Bool := false) : TacticM MkSimpContextResult := do
  if ctx && !stx[2].isNone then
    throwError "'simp_all' tactic does not support 'discharger' option"
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let simpOnly := !stx[3].isNone
  let simpTheorems ←
    if simpOnly then
      ({} : SimpTheorems).addConst ``eq_self
    else
      getSimpTheorems
  let congrTheorems ← getSimpCongrTheorems
  let r ← elabSimpArgs stx[4] (eraseLocal := eraseLocal) {
    config      := (← elabSimpConfig stx[1] (ctx := ctx))
    simpTheorems := #[simpTheorems], congrTheorems
  }
  if !r.starArg || ignoreStarArg then
    return { r with fvarIdToLemmaId := {}, dischargeWrapper }
  else
    let ctx := r.ctx
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    let mut fvarIdToLemmaId := {}
    for h in hs do
      let localDecl ← getLocalDecl h
      unless simpTheorems.isErased localDecl.userName do
        let fvarId := localDecl.fvarId
        let proof  := localDecl.toExpr
        let id     ← mkFreshUserName `h
        fvarIdToLemmaId := fvarIdToLemmaId.insert fvarId id
        simpTheorems ← simpTheorems.addTheorem proof (name? := id)
    let ctx := { ctx with simpTheorems }
    return { ctx, fvarIdToLemmaId, dischargeWrapper }

/--
`simpLocation ctx discharge? varIdToLemmaId loc`
runs the simplifier at locations specified by `loc`,
using the simp theorems collected in `ctx`
optionally running a discharger specified in `discharge?` on generated subgoals.
(Local hypotheses which have been added to the simp theorems must be recorded in
`fvarIdToLemmaId`.)

Its primary use is as the implementation of the
`simp [...] at ...` and `simp only [...] at ...` syntaxes,
but can also be used by other tactics when a `Syntax` is not available.

For many tactics other than the simplifier,
one should use the `withLocation` tactic combinator
when working with a `location`.
-/
def simpLocation (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (fvarIdToLemmaId : FVarIdToLemmaId := {}) (loc : Location) : TacticM Unit := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget fvarIdToLemmaId
  | Location.wildcard =>
    withMainContext do
      go (← getNondepPropHyps (← getMainGoal)) (simplifyTarget := true) fvarIdToLemmaId
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) (fvarIdToLemmaId : Lean.Meta.FVarIdToLemmaId) : TacticM Unit := do
    let mvarId ← getMainGoal
    let result? ← simpGoal mvarId ctx (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp) (fvarIdToLemmaId := fvarIdToLemmaId)
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]

/-
  "simp " (config)? (discharger)? ("only ")? ("[" simpLemma,* "]")? (location)?
-/
@[builtinTactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx => do
  let { ctx, fvarIdToLemmaId, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  dischargeWrapper.with fun discharge? =>
    simpLocation ctx discharge? fvarIdToLemmaId (expandOptLocation stx[5])

@[builtinTactic Lean.Parser.Tactic.simpAll] def evalSimpAll : Tactic := fun stx => do
  let { ctx, .. } ← mkSimpContext stx (eraseLocal := true) (ctx := true) (ignoreStarArg := true)
  match (← simpAll (← getMainGoal) ctx) with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [mvarId]

end Lean.Elab.Tactic
