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
  m : DoElabM Expr
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
  m := pure mi.m
  stM α := pure α
  runInBase e := pure e
  restoreCont dec := pure dec

def ControlStack.stateT (baseMonadInfo : MonadInfo) (mutVars : Array Name) (σ : Expr) (base : ControlStack) : ControlStack where
  description _ := m!"StateT {σ} over {base.description ()}"
  m := return mkApp2 (mkConst ``StateT [baseMonadInfo.u, baseMonadInfo.v]) (← getσ) (← base.m)
  stM α := stM α >>= base.stM
  runInBase e := do
    -- `e : StateT σ m α`. Fetch the state tuple `s : σ` and apply it to `e`, `e.run s`.
    -- See also `StateT.monadControl.liftWith`.
    let (tuple, tupleTy) ← mkProdMkN (← mutVars.mapM (getFVarFromUserName ·)) baseMonadInfo.u
    unless ← isDefEq tupleTy σ do -- just for sanity; maybe delete in the future
      throwError "State tuple type mismatch: expected {σ}, got {tupleTy}. This is a bug in the `do` elaborator."
    -- throwError "tuple: {tuple}, tupleTy: {tupleTy}, {σ}"
    -- let α ← mkFreshResultType `α
    -- let eTy := mkApp3 (mkConst ``StateT [mi.u, mi.v]) σ mi.m α
    -- let e ← Term.ensureHasType eTy e -- might need to replace mi.m by a metavariable due to match refinement
    base.runInBase <| mkApp e tuple
  restoreCont dec := do
    -- Wrap `dec` such that the result type is `(dec.resultType × σ)` by unpacking the state tuple
    -- before calling `dec.k`. See also `StateT.monadControl.restoreM`.
    let resultName ← mkFreshUserName `p
    let resultType ← stM dec.resultType
    let k : DoElabM Expr := do
      let p ← getFVarFromUserName resultName
      bindMutVarsFromTuple (dec.resultName :: mutVars.toList) p.fvarId! do
        dec.k
    base.restoreCont { resultName, resultType, k }
where
  getσ := do mkProdN (← mutVars.mapM (LocalDecl.type <$> getLocalDeclFromUserName ·)) baseMonadInfo.u
  stM α := return mkApp2 (mkConst ``Prod [baseMonadInfo.u, baseMonadInfo.u]) α (← getσ) -- NB: muts `σ` might have been refined by dependent pattern matches

def ControlStack.optionT (baseMonadInfo : MonadInfo) (optionTWrapper casesOnWrapper : Name)
    (getCont : DoElabM (DoElabM Expr)) (base : ControlStack) : ControlStack where
  description _ := m!"OptionT over {base.description ()}"
  m := return mkApp (mkConst optionTWrapper [baseMonadInfo.u, baseMonadInfo.v]) (← base.m)
  stM := base.stM ∘ stM
  runInBase e := do
    -- `e : OptionT m α`. Return `e`, which is defeq to `OptionT.run e`.
    -- See also `instMonadControlOptionTOfMonad.liftWith`.
    base.runInBase (← mkAppM ``OptionT.run #[e])
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
      return mkApp5 (mkConst casesOnWrapper [baseMonadInfo.u, baseMonadInfo.v]) dec.resultType β e kexit ksuccess
    base.restoreCont { resultName, resultType, k }
where
  stM α := mkApp (mkConst ``Option [baseMonadInfo.u]) α

def ControlStack.exceptT (baseMonadInfo : MonadInfo) (exceptTWrapper casesOnWrapper : Name)
    (getCont : DoElabM ReturnCont) (ε : Expr) (base : ControlStack) : ControlStack where
  description _ := m!"ExceptT ({ε}) over {base.description ()}"
  m := return mkApp2 (mkConst exceptTWrapper [baseMonadInfo.u, baseMonadInfo.v]) ε (← base.m)
  stM α := stM α >>= base.stM
  runInBase e := do
    -- `e : ExceptT ε m α`. Return `e`, which is defeq to `ExceptT.run e`.
    -- See also `instMonadControlExceptTOfMonad.liftWith`.
    base.runInBase (← mkAppM ``ExceptT.run #[e])
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
      return mkApp6 (mkConst casesOnWrapper [baseMonadInfo.u, baseMonadInfo.v]) ε dec.resultType β e kexit ksuccess
    let resultType ← stM dec.resultType
    base.restoreCont { resultName, resultType, k }
where
  -- Like `σ`, we need to refine `ε` because it is the early return value.
  stM α := return mkApp2 (mkConst ``Except [baseMonadInfo.u, baseMonadInfo.u]) (← getCont).resultType α

def ControlStack.earlyReturnT (baseMonadInfo : MonadInfo) (ρ : Expr) (m : ControlStack) : ControlStack :=
  exceptT baseMonadInfo ``EarlyReturnT ``EarlyReturn.runK getReturnCont ρ m

def ControlStack.breakT (baseMonadInfo : MonadInfo) (m : ControlStack) : ControlStack :=
  let getCont := getBreakCont >>= (·.getDM (throwError "`break` must be nested inside a loop"))
  optionT baseMonadInfo ``BreakT ``Break.runK getCont m

def ControlStack.continueT (baseMonadInfo : MonadInfo) (m : ControlStack) : ControlStack :=
  let getCont := getContinueCont >>= (·.getDM (throwError "`continue` must be nested inside a loop"))
  optionT baseMonadInfo ``ContinueT ``Continue.runK getCont m

private def mkInstMonad (mi : MonadInfo) : TermElabM Expr := do
  Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)

private def synthUsingDefEq (msg : String) (expected : Expr) (actual : Expr) : DoElabM Unit := do
  unless ← isDefEq expected actual do
    throwError "Failed to synthesize {msg}. {expected} is not definitionally equal to {actual}."

def ControlStack.mkBreak (base : ControlStack) (hasContinue : Bool) : DoElabM Expr := do
  let mi := { (← read).monadInfo with m := (← base.m) }
  let inst ← mkInstMonad mi
  let α ← mkFreshResultType `α
  -- When there's an outer `continue` layer as well, we account for that by applying `stM` of
  -- `OptionT` to `α`.
  let α := if hasContinue then mkApp (mkConst ``Option [mi.u]) α else α
  let mγ ← mkMonadicType (← read).doBlockResultType
  let res ← base.runInBase <| mkApp3 (mkConst ``BreakT.break [mi.u, mi.v]) α mi.m inst
  let ty ← inferType res
  -- Now instantiate `α`
  synthUsingDefEq "break result type" mγ ty
  return res

def ControlStack.mkContinue (base : ControlStack) : DoElabM Expr := do
  let mi := { (← read).monadInfo with m := (← base.m) }
  let inst ← mkInstMonad mi
  let α ← mkFreshResultType `α
  let mγ ← mkMonadicType (← read).doBlockResultType
  let res ← base.runInBase <| mkApp3 (mkConst ``ContinueT.continue [mi.u, mi.v]) α mi.m inst
  let ty ← inferType res
  -- Now instantiate `α`
  synthUsingDefEq "continue result type" mγ ty
  return res

def ControlStack.mkReturn (base : ControlStack) (r : Expr) : DoElabM Expr := do
  let mi := { (← read).monadInfo with m := (← base.m) }
  let instMonad ← mkInstMonad mi
  let ρ ← inferType r
  let δ ← mkFreshResultType `δ
  let mγ ← mkMonadicType (← read).doBlockResultType
  let mγ' := mkApp mi.m (mkApp2 (mkConst ``Except [mi.u, mi.v]) ρ δ)
  synthUsingDefEq "early return result type" mγ mγ'
  base.runInBase <| mkApp5 (mkConst ``EarlyReturnT.return [mi.u, mi.v]) ρ mi.m δ instMonad r

def ControlStack.mkPure (base : ControlStack) (resultName : Name) : DoElabM Expr := do
  let mi := { (← read).monadInfo with m := (← base.m) }
  let instMonad ← mkInstMonad mi
  let instPure := instMonad |> mkApp2 (mkConst ``Monad.toApplicative [mi.u, mi.v]) mi.m
                            |> mkApp2 (mkConst ``Applicative.toPure [mi.u, mi.v]) mi.m
  let r ← getFVarFromUserName resultName
  base.runInBase <| mkApp4 (mkConst ``Pure.pure [mi.u, mi.v]) mi.m instPure (← inferType r) r

structure ControlLifter where
  origCont : DoElemCont
  returnBase? : Option ControlStack
  breakBase? : Option ControlStack
  continueBase? : Option ControlStack
  pureBase : ControlStack
  pureDeadCode : CodeLiveness
  liftedDoBlockResultType : Expr

-- abbrev M := List
-- #reduce (types := true) M (Except Nat (Option (Option Bool) × String))
-- #reduce (types := true) OptionT (OptionT (StateT String (ExceptT Nat M))) Bool

def ControlLifter.ofCont (info : ControlInfo) (dec : DoElemCont) : DoElabM ControlLifter := do
  let mi := (← read).monadInfo
  let reassignedMutVars := (← read).mutVars |>.map (·.getId) |>.filter info.reassigns.contains
  let ρ := (← getReturnCont).resultType
  let σ ← mkProdN (← reassignedMutVars.mapM (LocalDecl.type <$> getLocalDeclFromUserName ·)) mi.u

  let needEarlyReturn := if info.returnsEarly then some ρ else none
  let needBreak := info.breaks && (← getBreakCont).isSome
  let needContinue := info.continues && (← getContinueCont).isSome
  let needState := if reassignedMutVars.isEmpty then none else some (reassignedMutVars, σ)
  let mut returnBase? := none
  let mut breakBase? := none
  let mut continueBase? := none
  let mut controlStack := ControlStack.base mi

  if let some ρ := needEarlyReturn then
    returnBase? := some controlStack -- Yes, this is correct. We need to store the super layer
    controlStack := ControlStack.earlyReturnT mi ρ controlStack
  if let some (reassignedMutVars, σ) := needState then
    controlStack := ControlStack.stateT mi reassignedMutVars σ controlStack
  if needBreak then
    breakBase? := some controlStack
    controlStack := ControlStack.breakT mi controlStack
  if needContinue then
    continueBase? := some controlStack
    controlStack := ControlStack.continueT mi controlStack
  return {
    origCont := dec,
    returnBase?,
    breakBase?,
    continueBase?,
    pureBase := controlStack,
    -- The success continuation `origCont` is dead code iff the `ControlInfo` says that there is no
    -- regular exit.
    pureDeadCode := if info.exitsRegularly then .alive else .deadSemantically,
    liftedDoBlockResultType := (← controlStack.stM dec.resultType),
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
  let breakCont :=
    match oldBreakCont, l.breakBase? with
    | some _, some breakBase => some <| breakBase.mkBreak (l.continueBase?.isSome)
    | _, _ => oldBreakCont
  let continueCont :=
    match oldContinueCont, l.continueBase? with
    | some _, some continueBase => some <| continueBase.mkContinue
    | _, _ => oldContinueCont
  let returnCont :=
    match l.returnBase? with
    | some returnBase => { oldReturnCont with k := returnBase.mkReturn }
    | _ => oldReturnCont
  let contInfo := ContInfo.toContInfoRef { breakCont, continueCont, returnCont }
  let pureCont := { l.origCont with k := l.pureBase.mkPure l.origCont.resultName, kind := .duplicable }
  withReader (fun ctx => { ctx with contInfo, doBlockResultType := l.liftedDoBlockResultType }) do
    elabElem pureCont

def ControlLifter.restoreCont (l : ControlLifter) : DoElabM DoElemCont := do
  l.pureBase.restoreCont { l.origCont with k := withDeadCode l.pureDeadCode l.origCont.k }
