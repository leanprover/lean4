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
  instMonad : Expr
  stM : Expr → Expr
  runInBase : Expr → DoElabM Expr
  restoreCont : DoElemCont → MetaM DoElemCont

def ControlStack.base (mi : MonadInfo) (instMonad : Expr) : ControlStack where
  description _ := "base"
  monadInfo := mi
  instMonad := instMonad
  stM α := α
  runInBase e := pure e
  restoreCont dec := pure dec

def ControlStack.stateT (reassignedMutVars : Array Name) (σ : Expr) (m : ControlStack) : ControlStack where
  description _ := m!"StateT ({σ}) over {m.description ()}"
  monadInfo :=
    { mi with m := mkApp2 (mkConst ``StateT [mi.u, mi.v]) σ mi.m }
  instMonad :=
    mkApp3 (mkConst ``StateT.instMonad [mi.u, mi.v]) σ mi.m m.instMonad
  stM := m.stM ∘ stM
  runInBase e := do
    -- `e : StateT σ m α`. Fetch the state tuple `s : σ` and apply it to `e`, `e.run s`.
    -- See also `StateT.monadControl.liftWith`.
    let (tuple, tupleTy) ← mkProdMkN (← reassignedMutVars.mapM (getFVarFromUserName ·))
    synthUsingDefEq "state tuple type" σ tupleTy
    discard <| Term.ensureHasType (mkSort (mkLevelSucc mi.u)) σ
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
  instMonad :=
    mkApp2 (mkConst ``OptionT.instMonad [mi.u, mi.v]) mi.m m.instMonad
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
    let k := do
      let e ← getFVarFromUserName resultName
      let outerCont ← getCont
      let kexit ← withLocalDeclD (← mkFreshUserName `r) (mkConst ``Unit) fun r => do
        mkLambdaFVars #[r] (← outerCont)
      let ksuccess ← withLocalDeclD dec.resultName dec.resultType fun r => do
        mkLambdaFVars #[r] (← dec.k)
      let β ← mkMonadicType (← read).doBlockResultType
      return mkApp5 (mkConst casesOnWrapper [mi.u, mi.v]) dec.resultType β e kexit ksuccess
    m.restoreCont { resultName, resultType, k }
where
  mi := m.monadInfo
  stM α := mkApp (mkConst ``Option [mi.u]) α

def ControlStack.exceptT (exceptTWrapper casesOnWrapper : Name)
    (getCont : DoElabM DoElemCont) (ρ : Expr) (m : ControlStack) : ControlStack where
  description _ := m!"ExceptT ({ρ}) over {m.description ()}"
  monadInfo :=
    { mi with m := mkApp2 (mkConst exceptTWrapper [mi.u, mi.v]) ρ mi.m }
  instMonad :=
    mkApp3 (mkConst ``ExceptT.instMonad [mi.u, mi.v]) ρ mi.m m.instMonad
  stM := m.stM ∘ stM
  runInBase e := do
    -- `e : ExceptT ρ m α`. Return `e`, which is defeq to `ExceptT.run e`.
    -- See also `instMonadControlExceptTOfMonad.liftWith`.
    m.runInBase (← mkAppM ``ExceptT.run #[e])
  restoreCont dec := do
    -- Wrap `dec` such that the result type is `Except ρ dec.resultType` by unpacking the exception,
    -- calling `dec.k` in the success case. See also `instMonadControlExceptTOfMonad.restoreM`.
    let resultName ← mkFreshUserName `e
    let resultType := stM dec.resultType
    let k := do
      let e ← getFVarFromUserName resultName
      let outerCont ← getCont
      let kexit ← withLocalDeclD outerCont.resultName outerCont.resultType fun r => do
        mkLambdaFVars #[r] (← outerCont.k)
      let ksuccess ← withLocalDeclD dec.resultName dec.resultType fun r => do
        mkLambdaFVars #[r] (← dec.k)
      let β ← mkMonadicType (← read).doBlockResultType
      return mkApp6 (mkConst casesOnWrapper [mi.u, mi.v]) ρ dec.resultType β e kexit ksuccess
    m.restoreCont { resultName, resultType, k }
where
  mi := m.monadInfo
  stM α := mkApp2 (mkConst ``Except [mi.u, mi.u]) ρ α

def ControlStack.earlyReturnT (ρ : Expr) (m : ControlStack) : ControlStack :=
  exceptT ``EarlyReturnT ``EarlyReturn.runK getReturnCont ρ m

def ControlStack.breakT (m : ControlStack) : ControlStack :=
  let getCont := getBreakCont >>= (·.getDM (throwError "`break` must be nested inside a loop"))
  optionT ``BreakT ``Break.runK getCont m

def ControlStack.continueT (m : ControlStack) : ControlStack :=
  let getCont := getContinueCont >>= (·.getDM (throwError "`continue` must be nested inside a loop"))
  optionT ``ContinueT ``Continue.runK getCont m

def ControlStack.synthesizeBreak (m : ControlStack) (kvar : ContVarId) (monadicResultType : Expr) : DoElabM Unit := do
  let mi := m.monadInfo
  let α ← mkFreshResultType `α
  kvar.synthesizeJumps do
    let m' := mkApp (mkConst ``BreakT [mi.u, mi.v]) mi.m
    discard <| isDefEq (mkApp m' α) monadicResultType
    m.runInBase <| mkApp3 (mkConst ``BreakT.break [mi.u, mi.v]) α mi.m m.instMonad

def ControlStack.synthesizeContinue (m : ControlStack) (kvar : ContVarId) (monadicResultType : Expr) : DoElabM Unit := do
  let mi := m.monadInfo
  let α ← mkFreshResultType `α
  kvar.synthesizeJumps do
    let m' := mkApp (mkConst ``ContinueT [mi.u, mi.v]) mi.m
    discard <| isDefEq (mkApp m' α) monadicResultType
    m.runInBase <| mkApp3 (mkConst ``ContinueT.continue [mi.u, mi.v]) α mi.m m.instMonad

def ControlStack.synthesizePure (m : ControlStack) (resultName : Name) (pureKVar : ContVarId) : DoElabM Unit := do
  let mi := m.monadInfo
  let instMonad := m.instMonad
  let instPure := instMonad |> mkApp2 (mkConst ``Monad.toApplicative [mi.u, mi.v]) mi.m
                            |> mkApp2 (mkConst ``Applicative.toPure [mi.u, mi.v]) mi.m
  pureKVar.synthesizeJumps do
    let r ← getFVarFromUserName resultName
    m.runInBase <| mkApp4 (mkConst ``Pure.pure [mi.u, mi.v])
      mi.m instPure (← inferType r) r

structure ControlLifter where
  mutVars : Array Name
  monadInfo : MonadInfo
  instMonad : Expr
  successCont : DoElemCont
  pureKVar : ContVarId
  breakKVar : ContVarId
  continueKVar : ContVarId
  returnCont : DoElemCont
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
  let pureKVar ← mkFreshContVar γ (mutVars.push dec.resultName)
  let returns ← IO.mkRef false
  let breakKVar ← mkFreshContVar γ mutVars
  let continueKVar ← mkFreshContVar γ mutVars
  let ρ := oldReturnCont.resultType
  let instMonad ← Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)
  -- We can fill in `returnK` immediately because it does not influence reassigned mut vars
  let δ ← mkFreshResultType `δ
  let returnCont := { oldReturnCont with k := do
    returns.set true
    let r ← getFVarFromUserName oldReturnCont.resultName
    let m' := mkApp2 (mkConst ``EarlyReturnT [mi.u, mi.v]) ρ mi.m
    discard <| isDefEq (mkApp m' δ) mγ
    return mkApp5 (mkConst ``EarlyReturnT.return [mi.u, mi.v]) ρ mi.m δ instMonad r }
  return {
    mutVars,
    monadInfo := mi,
    instMonad,
    successCont := dec,
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
  let pureCont := { l.successCont with k := l.pureKVar.mkJump, kind := .duplicable (pure := false) }
  withReader (fun ctx => { ctx with contInfo, doBlockResultType := l.resultType }) <| elabElem pureCont

def ControlLifter.synthesizeConts (l : ControlLifter)
    (continueT? : Option Bool := none)
    (breakT? : Option Bool := none)
    (stateT? : Option Bool := none)
    (earlyReturnT? : Option Bool := none) : DoElabM ControlStack := do
  let reassignedMutVars ← do
    let rootCtx := (← l.resultType.mvarId!.getDecl).lctx
    let pur ← l.pureKVar.getReassignedMutVars rootCtx
    let brk ← l.breakKVar.getReassignedMutVars rootCtx
    let cnt ← l.continueKVar.getReassignedMutVars rootCtx
    pure <| l.mutVars.filter (pur.union brk |>.union cnt).contains
  let continueT ← continueT?.getDM ((· > 0) <$> l.continueKVar.jumpCount)
  let breakT ← breakT?.getDM ((· > 0) <$> l.breakKVar.jumpCount)
  let stateT := stateT?.getD (reassignedMutVars.size > 0)
  let earlyReturnT ← earlyReturnT?.getDM l.returns.get
  let mut controlStack := ControlStack.base l.monadInfo l.instMonad
  if earlyReturnT then
    controlStack := ControlStack.earlyReturnT l.returnCont.resultType controlStack
  if stateT then
    let tys ← reassignedMutVars.mapM fun v => return (← getLocalDeclFromUserName v).type
    let σ ← mkProdN tys
    controlStack := ControlStack.stateT reassignedMutVars σ controlStack
  let mγ ← mkMonadicType l.resultType
  if breakT then
    controlStack.synthesizeBreak l.breakKVar mγ
    controlStack := ControlStack.breakT controlStack
  if continueT then
    controlStack.synthesizeContinue l.continueKVar mγ
    controlStack := ControlStack.continueT controlStack
  synthUsingDefEq "result type" l.resultType (controlStack.stM l.successCont.resultType)

  controlStack.synthesizePure l.successCont.resultName l.pureKVar
  return controlStack

def ControlLifter.restoreCont (l : ControlLifter) : DoElabM DoElemCont := do
  let controlStack ← l.synthesizeConts
  controlStack.restoreCont l.successCont
