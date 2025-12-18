/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
import Lean.Meta.ProdN
public import Lean.Elab.Do.Basic
import Init.Control.Do

public section

namespace Lean.Elab.Do

open Lean Meta Elab

structure ControlStack where
  description : Unit → MessageData
  monadInfo : MonadInfo
  stM : Expr → Expr
  runInBase : Expr → DoElabM Expr
  restoreCont : DoElemCont → MetaM DoElemCont

def ControlStack.unStM (m : ControlStack) (stMα : Expr) : DoElabM Expr := do
  let α ← mkFreshResultType `α
  let stMα' ← Term.substituteRefinedDiscriminants (m.stM α)
  unless ← isDefEq stMα stMα' do
    throwError "Could not take apart {stMα} as a `{stMα'}`. This is a bug in the `do` elaborator."
  return α

def ControlStack.base (mi : MonadInfo) : ControlStack where
  description _ := "base"
  monadInfo := mi
  stM α := α
  runInBase e := pure e
  restoreCont dec := pure dec

def ControlStack.stateT (reassignedMutVars : Array Name) (σ : Expr) (m : ControlStack) : ControlStack where
  description _ := m!"StateT ({σ}) over {m.description ()}"
  monadInfo :=
    { mi with m := mkApp2 (mkConst ``StateT [mi.u, mi.v]) σ mi.m }
  stM := m.stM ∘ stM
  runInBase e := do
    -- `e : StateT σ m α`. Fetch the state tuple `s : σ` and apply it to `e`, `e.run s`.
    -- See also `StateT.monadControl.liftWith`.
    let (tuple, tupleTy) ← mkProdMkN (← reassignedMutVars.mapM (getFVarFromUserName ·)) (mkLevelSucc mi.u)
    let σ ← Term.substituteRefinedDiscriminants σ
    unless ← isDefEq tupleTy σ do -- just for sanity; maybe delete in the future
      throwError "State tuple type mismatch: expected {σ}, got {tupleTy}. This is a bug in the `do` elaborator."
    let α ← mkFreshResultType `α
    let eTy ← Term.substituteRefinedDiscriminants (mkApp3 (mkConst ``StateT [mi.u, mi.v]) σ mi.m α)
    let e ← Term.ensureHasType eTy e -- might need to replace mi.m by a metavariable due to match refinement
    m.runInBase <| mkApp e tuple
  restoreCont dec := do
    -- Wrap `dec` such that the result type is `(dec.resultType × σ)` by unpacking the state tuple
    -- before calling `dec.k`. See also `StateT.monadControl.restoreM`.
    let resultName ← mkFreshUserName `p
    let resultType := stM dec.resultType
    let k := do
      let p ← getFVarFromUserName resultName
      bindMutVarsFromTuple (dec.resultName :: reassignedMutVars.toList) p.fvarId! do
        dec.k
    m.restoreCont { resultName, resultType, k }
where
  mi := m.monadInfo
  stM α := mkApp2 (mkConst ``Prod [mi.u, mi.u]) α σ

def ControlStack.optionT (optionTWrapper casesOnWrapper : Name)
    (getCont : DoElabM (DoElabM Expr)) (m : ControlStack) : ControlStack where
  description _ := m!"OptionT over {m.description ()}"
  monadInfo :=
    { mi with m := mkApp (mkConst optionTWrapper [mi.u, mi.v]) mi.m }
  stM := m.stM ∘ stM
  runInBase e := do
    -- `e : OptionT m α`. Return `e`, which is defeq to `OptionT.run e`.
    -- See also `instMonadControlOptionTOfMonad.liftWith`.
    m.runInBase (← mkAppM ``OptionT.run #[e])
  restoreCont dec := do
    -- Wrap `dec` such that the result type is `Option dec.resultType` by unpacking
    -- the option, calling `dec.k` in the success case.
    -- See also `instMonadControlOptionTOfMonad.restoreM`.
    let resultName ← mkFreshUserName `e
    let resultType := stM dec.resultType
    let k : DoElabM Expr := do
      let e ← getFVarFromUserName resultName
      let outerCont ← getCont
      let kexit ← withLocalDeclD (← mkFreshUserName `r) (mkConst ``Unit) fun r => do
        mkLambdaFVars #[r] (← outerCont)
      let ksuccess ← withLocalDeclD dec.resultName dec.resultType fun r => do
        mkLambdaFVars #[r] (← dec.k)
      let β ← mkMonadicType (← getRefinedDoBlockResultType)
      return mkApp5 (mkConst casesOnWrapper [mi.u, mi.v]) dec.resultType β e kexit ksuccess
    m.restoreCont { resultName, resultType, k }
where
  mi := m.monadInfo
  stM α := mkApp (mkConst ``Option [mi.u]) α

def ControlStack.exceptT (exceptTWrapper casesOnWrapper : Name)
    (getCont : DoElabM ReturnCont) (ε : Expr) (m : ControlStack) : ControlStack where
  description _ := m!"ExceptT ({ε}) over {m.description ()}"
  monadInfo :=
    { mi with m := mkApp2 (mkConst exceptTWrapper [mi.u, mi.v]) ε mi.m }
  stM := m.stM ∘ stM
  runInBase e := do
    -- `e : ExceptT ε m α`. Return `e`, which is defeq to `ExceptT.run e`.
    -- See also `instMonadControlExceptTOfMonad.liftWith`.
    m.runInBase (← mkAppM ``ExceptT.run #[e])
  restoreCont dec := do
    -- Wrap `dec` such that the result type is `Except ε dec.resultType` by unpacking the exception,
    -- calling `dec.k` in the success case. See also `instMonadControlExceptTOfMonad.restoreM`.
    let resultName ← mkFreshUserName `e
    let k := do
      let e ← getFVarFromUserName resultName
      let outerCont ← getCont
      let decResultType ← Term.substituteRefinedDiscriminants dec.resultType
      let exitResTy ← Term.substituteRefinedDiscriminants outerCont.resultType
      let kexit ← withLocalDeclD (← mkFreshUserName `r) exitResTy fun r => do
        mkLambdaFVars #[r] (← outerCont.k r)
      let (ksuccess, β) ← withLocalDeclD dec.resultName decResultType fun r => do
        let body ← dec.k
        let ksuccess ← mkLambdaFVars #[r] body
        let β ← inferType body
        return (ksuccess, β)
      return mkApp6 (mkConst casesOnWrapper [mi.u, mi.v]) ε decResultType β e kexit ksuccess
    let resultType := stM dec.resultType
    m.restoreCont { resultName, resultType, k }
where
  mi := m.monadInfo
  stM α := mkApp2 (mkConst ``Except [mi.u, mi.u]) ε α

def ControlStack.earlyReturnT (ρ : Expr) (m : ControlStack) : ControlStack :=
  exceptT ``EarlyReturnT ``EarlyReturn.runK getReturnCont ρ m

def ControlStack.breakT (m : ControlStack) : ControlStack :=
  let getCont := getBreakCont >>= (·.getDM (throwError "`break` must be nested inside a loop"))
  optionT ``BreakT ``Break.runK getCont m

def ControlStack.continueT (m : ControlStack) : ControlStack :=
  let getCont := getContinueCont >>= (·.getDM (throwError "`continue` must be nested inside a loop"))
  optionT ``ContinueT ``Continue.runK getCont m

private def mkInstMonad (mi : MonadInfo) : TermElabM Expr := do
  Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)

def ControlStack.synthesizeBreak (m : ControlStack) (kvar : ContVarId) (monadicResultType : Expr) : DoElabM Unit := do
  let mi := m.monadInfo
  let inst ← mkInstMonad mi
  let m' := mkApp (mkConst ``BreakT [mi.u, mi.v]) mi.m
  let α ← mkFreshResultType `α
  if (← kvar.jumpCount) > 0 then
    discard <| isDefEq (mkApp m' α) monadicResultType
  kvar.synthesizeJumps do
    let α ← Term.substituteRefinedDiscriminants α
    m.runInBase <| mkApp3 (mkConst ``BreakT.break [mi.u, mi.v]) α mi.m inst

def ControlStack.synthesizeContinue (m : ControlStack) (kvar : ContVarId) (monadicResultType : Expr) : DoElabM Unit := do
  let mi := m.monadInfo
  let inst ← mkInstMonad mi
  let m' := mkApp (mkConst ``ContinueT [mi.u, mi.v]) mi.m
  let α ← mkFreshResultType `α
  if (← kvar.jumpCount) > 0 then
    discard <| isDefEq (mkApp m' α) monadicResultType
  kvar.synthesizeJumps do
    let α ← Term.substituteRefinedDiscriminants α
    m.runInBase <| mkApp3 (mkConst ``ContinueT.continue [mi.u, mi.v]) α mi.m inst

def ControlStack.synthesizePure (m : ControlStack) (resultName : Name) (pureKVar : ContVarId) : DoElabM Unit := do
  let mi := m.monadInfo
  let instMonad ← mkInstMonad mi
  let instPure := instMonad |> mkApp2 (mkConst ``Monad.toApplicative [mi.u, mi.v]) mi.m
                            |> mkApp2 (mkConst ``Applicative.toPure [mi.u, mi.v]) mi.m
  pureKVar.synthesizeJumps do
    let r ← getFVarFromUserName resultName
    m.runInBase <| mkApp4 (mkConst ``Pure.pure [mi.u, mi.v]) mi.m instPure (← inferType r) r

structure ControlLifter where
  mutVars : Array Name
  monadInfo : MonadInfo
  instMonad : Expr
  successCont : DoElemCont
  pureKVar : ContVarId
  breakKVar : ContVarId
  continueKVar : ContVarId
  returnCont : ReturnCont
  returns : IO.Ref Bool
  resultType : Expr

def ControlLifter.ofCont (dec : DoElemCont) : DoElabM ControlLifter := do
  let mi := (← read).monadInfo
  let oldReturnCont ← getReturnCont
  -- γ is the result type of the `try` block. It is `stM m (t m)` for whatever `t` is necessary
  -- to restore reassigned mut vars, early `return`, `break` and `continue`.
  let γ ← mkFreshResultType `γ
  let mγ ← mkMonadicType γ
  let mutVars := (← read).mutVars |>.map (·.getId)
  let pureKVar ← mkFreshContVar (mutVars.push dec.resultName)
  let returns ← IO.mkRef false
  let breakKVar ← mkFreshContVar mutVars
  let continueKVar ← mkFreshContVar mutVars
  let instMonad ← Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)
  -- We can fill in `returnK` immediately because it does not influence reassigned mut vars
  return {
  let returnCont := { oldReturnCont with  -- NB: Keep the old `getResultType`.
      k r := do
        returns.set true
        let ρ ← Term.substituteRefinedDiscriminants oldReturnCont.resultType
        let r ← Term.ensureHasType ρ r
        let m' := mkApp2 (mkConst ``EarlyReturnT [mi.u, mi.v]) ρ mi.m
        let δ ← mkFreshResultType `δ
        discard <| isDefEq (mkApp m' δ) mγ -- TODO: Try `getDoBlockResultType` instead of `γ`?
        return mkApp5 (mkConst ``EarlyReturnT.return [mi.u, mi.v]) ρ mi.m δ instMonad r
    }
  -- We want to elaborate the continuation in the original, current context.
  -- In particular, it should pick up the original `getDoBlockResultType`, not the one that contains
  -- the `stM` of the current control stack.
  let successCont := { dec with k := withReader (fun _ => oldCtx) dec.k }
    mutVars,
    monadInfo := mi,
    instMonad,
    successCont,
    pureKVar,
    breakKVar,
    continueKVar,
    returnCont,
    returns,
    resultType := γ
  }

def ControlLifter.lift (l : ControlLifter) (elabElem : DoElemCont → DoElabM Expr) : DoElabM Expr := do
  let oldBreakCont ← getBreakCont
  let oldContinueCont ← getContinueCont
  let breakCont := Functor.mapConst l.breakKVar.mkJump oldBreakCont
  let continueCont := Functor.mapConst l.continueKVar.mkJump oldContinueCont
  let returnCont := l.returnCont
  let contInfo := ContInfo.toContInfoRef { breakCont, continueCont, returnCont }
  let pureCont := { l.successCont with k := l.pureKVar.mkJump, kind := .duplicable }
  withReader (fun ctx => { ctx with contInfo }) <| elabElem pureCont

def ControlLifter.synthesizeConts (l : ControlLifter)
    (continueT? : Option Bool := none)
    (breakT? : Option Bool := none)
    (stateT? : Option Bool := none)
    (earlyReturnT? : Option Bool := none) : DoElabM ControlStack := do
  let reassignedMutVars ← do
    let rootCtx := (← l.pureKVar.find).lctx
    let pur ← l.pureKVar.getReassignedMutVars rootCtx
    let brk ← l.breakKVar.getReassignedMutVars rootCtx
    let cnt ← l.continueKVar.getReassignedMutVars rootCtx
    pure <| l.mutVars.filter (pur.union brk |>.union cnt).contains
  let mut controlStack := ControlStack.base l.monadInfo
  let mut breakStack := none
  let mut continueStack := none
  let σ ← mkFreshResultType `σ
  if ← earlyReturnT?.getDM l.returns.get then
    controlStack := ControlStack.earlyReturnT l.returnCont.resultType controlStack
  if stateT?.getD (reassignedMutVars.size > 0) then
    controlStack := ControlStack.stateT reassignedMutVars σ controlStack
  if ← breakT?.getDM ((· > 0) <$> l.breakKVar.jumpCount) then
    controlStack := ControlStack.breakT controlStack
    breakStack := some controlStack
  if ← continueT?.getDM ((· > 0) <$> l.continueKVar.jumpCount) then
    controlStack := ControlStack.continueT controlStack
    continueStack := some controlStack
  let mut γ ← getRefinedDoBlockResultType
  synthUsingDefEq "result type" γ (← Term.substituteRefinedDiscriminants (controlStack.stM l.successCont.resultType))
  -- Now propagate back to the `break` and `continue` jump sites
  if let some stk := continueStack then
    stk.synthesizeContinue l.continueKVar (← mkMonadicType γ)
    let γ' ← mkFreshResultType `γ
    synthUsingDefEq "result type" γ' (← Term.substituteRefinedDiscriminants (stk.stM l.successCont.resultType))
    γ := γ'
  if let some stk := breakStack then
    stk.synthesizeBreak l.breakKVar (← mkMonadicType γ)

  controlStack.synthesizePure l.successCont.resultName l.pureKVar
  return controlStack

def ControlLifter.restoreCont (l : ControlLifter) : DoElabM DoElemCont := do
  let controlStack ← l.synthesizeConts
  -- The success continuation `l.successCont` is dead code iff `l.pureKVar` is.
  -- However, we need to generate code for it, so we relax its flag to `.deadSemantically`.
  let deadCode := (← l.pureKVar.getDeadCode).lub .deadSemantically
  controlStack.restoreCont { l.successCont with k := withDeadCode deadCode l.successCont.k }
