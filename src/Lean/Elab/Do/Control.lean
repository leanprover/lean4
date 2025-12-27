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
  stM : Expr → DoElabM Expr
  runInBase : Expr → DoElabM Expr
  restoreCont : DoElemCont → DoElabM DoElemCont

def ControlStack.unStM (m : ControlStack) (stMα : Expr) : DoElabM Expr := do
  let α ← mkFreshResultType `α
  let stMα' ← m.stM α
  unless ← isDefEq stMα stMα' do
    throwError "Could not take apart {stMα} as a `{stMα'}`. This is a bug in the `do` elaborator."
  return α

def ControlStack.base (mi : MonadInfo) : ControlStack where
  description _ := "base"
  monadInfo := mi
  stM α := pure α
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
    let (tuple, tupleTy) ← mkProdMkN (← reassignedMutVars.mapM (getFVarFromUserName ·)) mi.u
    unless ← isDefEq tupleTy σ do -- just for sanity; maybe delete in the future
      throwError "State tuple type mismatch: expected {σ}, got {tupleTy}. This is a bug in the `do` elaborator."
    -- throwError "tuple: {tuple}, tupleTy: {tupleTy}, {σ}"
    -- let α ← mkFreshResultType `α
    -- let eTy := mkApp3 (mkConst ``StateT [mi.u, mi.v]) σ mi.m α
    -- let e ← Term.ensureHasType eTy e -- might need to replace mi.m by a metavariable due to match refinement
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
  stM α := mkApp2 (mkConst ``Prod [mi.u, mi.u]) α σ -- NB: let muts `σ` are never refined by dependent pattern matches

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
      let β ← mkMonadicType (← read).doBlockResultType
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
  stM α := m.stM α >>= stM
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
      let kexit ← withLocalDeclD (← mkFreshUserName `r) outerCont.resultType fun r => do
        mkLambdaFVars #[r] (← outerCont.k r)
      let (ksuccess, β) ← withLocalDeclD dec.resultName dec.resultType fun r => do
        let body ← dec.k
        let ksuccess ← mkLambdaFVars #[r] body
        let β ← inferType body
        return (ksuccess, β)
      return mkApp6 (mkConst casesOnWrapper [mi.u, mi.v]) ε dec.resultType β e kexit ksuccess
    let resultType ← stM dec.resultType
    m.restoreCont { resultName, resultType, k }
where
  mi := m.monadInfo
  -- In contrast to `σ`, we need to refine `ε` because it is the early return value.
  stM α := return mkApp2 (mkConst ``Except [mi.u, mi.u]) (← getCont).resultType α

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

def ControlStack.synthesizeBreakContinue (breakTName breakName : Name) (m : ControlStack) (kvar : ContVarId) (mstMγ : Expr) : DoElabM Unit := do
  let mi := m.monadInfo
  let inst ← mkInstMonad mi
  let m' := mkApp (mkConst breakTName [mi.u, mi.v]) mi.m
  let α ← mkFreshResultType `α
  -- trace[Elab.do] "synthesizeBreakContinue: {mkApp m' α}, {mstMγ}"
  synthUsingDefEq "break/continue result type" (mkApp m' α) mstMγ
  kvar.synthesizeJumps do
    m.runInBase <| mkApp3 (mkConst breakName [mi.u, mi.v]) α mi.m inst

def ControlStack.synthesizeContinue := synthesizeBreakContinue ``ContinueT ``ContinueT.continue
def ControlStack.synthesizeBreak := synthesizeBreakContinue ``BreakT ``BreakT.break

def ControlStack.synthesizeReturn (m : ControlStack) (resultName : Name) (returnKVar : ContVarId) (mstMγ : Expr) : DoElabM Unit := do
  let mi := m.monadInfo
  let instMonad ← mkInstMonad mi
  returnKVar.synthesizeJumps do
    let r ← getFVarFromUserName resultName
    let ρ ← inferType r
    -- mstMγ is not dependently refined my pattern matches, hence its ρ will not be either.
    -- So we'll match out *some* ρ' and throw it away; we know that it's defeq to ρ modulo refinements.
    let ρ' ← mkFreshResultType `ρ
    let δ ← mkFreshResultType `δ
    let stMγ := mkApp2 (mkConst ``Except [mi.u, mi.v]) ρ' δ
    synthUsingDefEq "early return result type" (mkApp mi.m stMγ) mstMγ
    return mkApp5 (mkConst ``EarlyReturnT.return [mi.u, mi.v]) ρ mi.m δ instMonad r

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
  origCont : DoElemCont
  pureKVar : ContVarId
  returnKVar : ContVarId
  breakKVar : ContVarId
  continueKVar : ContVarId
  /--
  The result type of the lifted `do` block; if `γ` is the original result type, then this is
  `stM m (t m) γ`. We do not know `t` until we have seen all `lift` calls, hence this field starts
  out as a metavariable.
  -/
  stMγ : Expr

def ControlLifter.ofCont (dec : DoElemCont) : DoElabM ControlLifter := do
  -- stMγ is the result type of the `try` block. It is `stM m (t m)` for whatever `t` is necessary
  -- to restore reassigned mut vars, early `return`, `break` and `continue`.
  -- The `stM m` is constructed by one of the continuations.
  let stMγ ← mkFreshResultType `stMγ .synthetic
  let mutVars := (← read).mutVars |>.map (·.getId)
  let pureKVar ← mkFreshContVar (mutVars.push dec.resultName)
  let returnKVar ← mkFreshContVar (mutVars.push dec.resultName)
  let breakKVar ← mkFreshContVar mutVars
  let continueKVar ← mkFreshContVar mutVars
  return {
    mutVars,
    origCont := dec,
    pureKVar,
    returnKVar,
    breakKVar,
    continueKVar,
    stMγ
  }

/--
This function is like `MonadControl.liftWith fun runInBase => elabElem (runInBase pure)`.
All continuations should be thought of as wrapped in `runInBase`, so that their effects are embedded
in the terminal `stM m (t m)` result type. This wrapping will be realized by
`ControlStack.synthesizeConts`, after we know what the transformer stack `t` looks like.
What `t` looks like depends on whether reassignments, early `return`, `break` and `continue` are
used, considering *all* the use sites of `ControlLifter.lift`.
-/
def ControlLifter.lift (l : ControlLifter) (elabElem : DoElemCont → DoElabM Expr) : DoElabM Expr := do
  let oldBreakCont ← getBreakCont
  let oldContinueCont ← getContinueCont
  let oldReturnCont ← getReturnCont
  let breakCont := Functor.mapConst l.breakKVar.mkJump oldBreakCont
  let continueCont := Functor.mapConst l.continueKVar.mkJump oldContinueCont
  let returnCont := { oldReturnCont with k r := do
      mapLetDeclZeta l.origCont.resultName (← inferType r) r (nondep := true) (kind := .implDetail)
        fun _ => l.returnKVar.mkJump
    }
  let contInfo := ContInfo.toContInfoRef { breakCont, continueCont, returnCont }
  let pureCont := { l.origCont with k := l.pureKVar.mkJump, kind := .duplicable }
  withReader (fun ctx => { ctx with contInfo, doBlockResultType := l.stMγ }) do
    withSynthesizeForDo (elabElem pureCont)

def ControlLifter.restoreCont (l : ControlLifter)
    (continueT? : Option Bool := none)
    (breakT? : Option Bool := none)
    (stateT? : Option Bool := none)
    (earlyReturnT? : Option Bool := none) : DoElabM DoElemCont := do
  let reassignedMutVars ← do
    let rootCtx := (← l.pureKVar.find).lctx
    let pur ← l.pureKVar.getReassignedMutVars rootCtx
    let brk ← l.breakKVar.getReassignedMutVars rootCtx
    let cnt ← l.continueKVar.getReassignedMutVars rootCtx
    pure <| l.mutVars.filter (pur.union brk |>.union cnt).contains
  let mut controlStack := ControlStack.base (← read).monadInfo
  let mut returnBase := none
  let mut breakBase := none
  let mut continueBase := none
  let σ ← l.stMγ.mvarId!.withContext do mkFreshResultType `σ
  if ← earlyReturnT?.getDM ((· > 0) <$> l.returnKVar.jumpCount) then
    returnBase := some controlStack -- Yes, this is correct. We need to store the super layer
    controlStack := ControlStack.earlyReturnT (← getReturnCont).resultType controlStack
  if stateT?.getD (reassignedMutVars.size > 0) then
    controlStack := ControlStack.stateT reassignedMutVars σ controlStack
  if ← breakT?.getDM ((· > 0) <$> l.breakKVar.jumpCount) then
    breakBase := some controlStack
    controlStack := ControlStack.breakT controlStack
  if ← continueT?.getDM ((· > 0) <$> l.continueKVar.jumpCount) then
    continueBase := some controlStack
    controlStack := ControlStack.continueT controlStack
  let ty ← controlStack.stM l.origCont.resultType
  -- trace[Elab.do] "before {σ}, {controlStack.description ()}, {l.stMγ}, {ty}"
  withOptions (fun o =>
    if o.getBool `trace.Elab.do then
      o |>.setBool `trace.Meta.isDefEq true
    else
      o) do synthUsingDefEq "result type" l.stMγ ty
  let mut tmγ := mkApp controlStack.monadInfo.m l.origCont.resultType
  -- Now propagate back to the `break` and `continue` jump sites
  if let some stk := continueBase then
    stk.synthesizeContinue l.continueKVar tmγ
  if let some stk := breakBase then
    stk.synthesizeBreak l.breakKVar tmγ
  if let some stk := returnBase then
    stk.synthesizeReturn l.origCont.resultName l.returnKVar (← mkMonadicType l.stMγ)

  controlStack.synthesizePure l.origCont.resultName l.pureKVar

  -- The success continuation `l.origCont` is dead code iff `l.pureKVar` is.
  -- However, we need to generate code for it, so we relax its flag to `.deadSemantically`.
  let deadCode := (← l.pureKVar.getDeadCode).lub .deadSemantically
  controlStack.restoreCont { l.origCont with k := withDeadCode deadCode l.origCont.k }
