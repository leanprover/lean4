/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/

/-!
The top-down analyzer is an optional preprocessor to the delaborator that aims
to determine the minimal annotations necessary to ensure that the delaborated
expression can be re-elaborated correctly. Currently, the top-down analyzer
is neither sound nor complete: there may be edge-cases in which the expression
can still not be re-elaborated correctly, and it may also add many annotations
that are not strictly necessary.
-/

import Lean.Meta
import Lean.Util.CollectLevelParams
import Lean.Util.ReplaceLevel
import Lean.PrettyPrinter.Delaborator.Options
import Lean.PrettyPrinter.Delaborator.SubExpr
import Std.Data.RBMap

namespace Lean

open Lean.Meta
open Std (RBMap)

register_builtin_option pp.analyze : Bool := {
  defValue := true
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) determine annotations sufficient to ensure round-tripping"
}

register_builtin_option pp.analyze.checkInstances : Bool := {
  -- TODO: It would be great to make this default to `true`, but currently, `MessageData` does not
  -- include the `LocalInstances`, so this will be very over-aggressive in inserting instances
  -- that would otherwise be easy to synthesize. We may consider threading the instances in the future,
  -- or at least tracking a bool for whether the instances have been lost.
  defValue := false
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) confirm that instances can be re-synthesized"
}

register_builtin_option pp.analyze.typeAscriptions : Bool := {
  defValue := true
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) add type ascriptions when deemed necessary"
}

register_builtin_option pp.analyze.trustSubst : Bool := {
  defValue := false
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) always 'pretend' applications that can delab to ▸ are 'regular'"
}

register_builtin_option pp.analyze.trustOfNat : Bool := {
  defValue := true
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) always 'pretend' `OfNat.ofNat` applications can elab bottom-up"
}

register_builtin_option pp.analyze.trustOfScientific : Bool := {
  defValue := true
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) always 'pretend' `OfScientific.ofScientific` applications can elab bottom-up"
}

register_builtin_option pp.analyze.trustCoe : Bool := {
  defValue := false
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) always assume a coercion can be correctly inserted"
}

register_builtin_option pp.analyze.trustId : Bool := {
  defValue := true
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) always assume an implicit `fun x => x` can be inferred"
}

register_builtin_option pp.analyze.trustKnownFOType2TypeHOFuns : Bool := {
  defValue := true
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) omit higher-order functions whose values seem to be knownType2Type"
}

register_builtin_option pp.analyze.omitMax : Bool := {
  defValue := true
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) omit universe `max` annotations (these constraints can actually hurt)"
}

register_builtin_option pp.analyze.knowsType : Bool := {
  defValue := true
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) assume the type of the original expression is known"
}

def getPPAnalyze                            (o : Options) : Bool := o.get pp.analyze.name pp.analyze.defValue
def getPPAnalyzeCheckInstances              (o : Options) : Bool := o.get pp.analyze.checkInstances.name pp.analyze.checkInstances.defValue
def getPPAnalyzeTypeAscriptions             (o : Options) : Bool := o.get pp.analyze.typeAscriptions.name pp.analyze.typeAscriptions.defValue
def getPPAnalyzeTrustSubst                  (o : Options) : Bool := o.get pp.analyze.trustSubst.name pp.analyze.trustSubst.defValue
def getPPAnalyzeTrustOfNat                  (o : Options) : Bool := o.get pp.analyze.trustOfNat.name pp.analyze.trustOfNat.defValue
def getPPAnalyzeTrustOfScientific           (o : Options) : Bool := o.get pp.analyze.trustOfScientific.name pp.analyze.trustOfScientific.defValue
def getPPAnalyzeTrustId                     (o : Options) : Bool := o.get pp.analyze.trustId.name pp.analyze.trustId.defValue
def getPPAnalyzeTrustCoe                    (o : Options) : Bool := o.get pp.analyze.trustCoe.name pp.analyze.trustCoe.defValue
def getPPAnalyzeTrustKnownFOType2TypeHOFuns (o : Options) : Bool := o.get pp.analyze.trustKnownFOType2TypeHOFuns.name pp.analyze.trustKnownFOType2TypeHOFuns.defValue
def getPPAnalyzeOmitMax                     (o : Options) : Bool := o.get pp.analyze.omitMax.name pp.analyze.omitMax.defValue
def getPPAnalyzeKnowsType                   (o : Options) : Bool := o.get pp.analyze.knowsType.name pp.analyze.knowsType.defValue

def getPPAnalysisSkip          (o : Options) : Bool := o.get `pp.analysis.skip false
def getPPAnalysisHole          (o : Options) : Bool := o.get `pp.analysis.hole false
def getPPAnalysisNamedArg      (o : Options) : Bool := o.get `pp.analysis.namedArg false
def getPPAnalysisLetVarType    (o : Options) : Bool := o.get `pp.analysis.letVarType false
def getPPAnalysisNeedsType     (o : Options) : Bool := o.get `pp.analysis.needsType false
def getPPAnalysisNeedsExplicit (o : Options) : Bool := o.get `pp.analysis.needsExplicit false

namespace PrettyPrinter.Delaborator

def returnsPi (motive : Expr) : MetaM Bool := do
  lambdaTelescope motive fun xs b => b.isForall

def isNonConstFun (motive : Expr) : MetaM Bool := do
  match motive with
  | Expr.lam name d b _ => isNonConstFun b
  | _ => motive.hasLooseBVars

def isSimpleHOFun (motive : Expr) : MetaM Bool := do
  not (← returnsPi motive) && not (← isNonConstFun motive)

def isType2Type (motive : Expr) : MetaM Bool := do
  match ← inferType motive with
  | Expr.forallE _ (Expr.sort ..) (Expr.sort ..) .. => true
  | _ => false

def isFOLike (motive : Expr) : MetaM Bool := do
  let f := motive.getAppFn
  f.isFVar || f.isConst

def isIdLike (arg : Expr) : Bool := do
  -- TODO: allow `id` constant as well?
  match arg with
  | Expr.lam _ _ (Expr.bvar ..) .. => true
  | _ => false

def isCoe (e : Expr) : Bool :=
  -- TODO: `coeSort? Builtins doesn't seem to render them anyway
  e.isAppOfArity `coe 4
  || (e.isAppOf `coeFun && e.getAppNumArgs >= 4)
  || e.isAppOfArity `coeSort 4

namespace TopDownAnalyze

private def valUnknown (e : Expr) : MetaM Bool := do
  (← instantiateMVars e).hasMVar

private def typeUnknown (e : Expr) : MetaM Bool := do
  (← instantiateMVars (← inferType e)).hasMVar


def isHBinOp (e : Expr) : Bool := do
  -- TODO: instead of tracking these explicitly,
  -- consider a more general solution that checks for defaultInstances
  if e.getAppNumArgs != 6 then return false
  let f := e.getAppFn
  if !f.isConst then return false

  -- Note: we leave out `HPow.hPow because we expect its homogeneous
  -- version will change soon
  let ops := #[
    `HOr.hOr, `HXor.hXor, `HAnd.hAnd,
    `HAppend.hAppend, `HOrElse.hOrElse, `HAndThen.hAndThen,
    `HAdd.hAdd, `HSub.hSub, `HMul.hMul, `HDiv.hDiv, `HMod.hMod,
    `HShiftLeft.hShiftLeft, `HShiftRight]
  ops.any fun op => op == f.constName!

def replaceLPsWithVars (e : Expr) : MetaM Expr := do
  let lps := collectLevelParams {} e |>.params
  let mut replaceMap : Std.HashMap Name Level := {}
  for lp in lps do replaceMap := replaceMap.insert lp (← mkFreshLevelMVar)
  return e.replaceLevel fun
    | Level.param n .. => replaceMap.find! n
    | l => if !l.hasParam then some l else none

def isDefEqAssigning (t s : Expr) : MetaM Bool := do
  withReader (fun ctx => { ctx with config := { ctx.config with assignSyntheticOpaque := true }}) $
    Meta.isDefEq t s

def checkpointDefEq (t s : Expr) : MetaM Bool := do
  Meta.checkpointDefEq (mayPostpone := false) do
    withTransparency TransparencyMode.instances do
      isDefEqAssigning t s

def tryUnify (t s : Expr) : MetaM Unit := do
  try
    let r ← isDefEqAssigning t s
    if !r then trace[pp.analyze.tryUnify] "warning: isDefEq returned false"
    pure ()
  catch ex =>
    trace[pp.analyze.tryUnify] "warning: isDefEq threw"
    pure ()

partial def inspectOutParams (arg mvar : Expr) : MetaM Unit := do
  let argType  ← inferType arg -- HAdd α α α
  let mvarType ← inferType mvar
  let fType ← inferType argType.getAppFn -- Type → Type → outParam Type
  let mType ← inferType mvarType.getAppFn
  inspectAux fType mType 0 argType.getAppArgs mvarType.getAppArgs
where
  inspectAux (fType mType : Expr) (i : Nat) (args mvars : Array Expr) := do
    let fType ← whnf fType
    let mType ← whnf mType
    if not (i < args.size) then return ()
    match fType, mType with
    | Expr.forallE _ fd fb _, Expr.forallE _ md mb _ => do
      -- TODO: do I need to check (← okBottomUp? args[i] mvars[i] fuel).isSafe here?
      -- if so, I'll need to take a callback
      if isOutParam fd then
        tryUnify (args[i]) (mvars[i])
      inspectAux (fb.instantiate1 args[i]) (mb.instantiate1 mvars[i]) (i+1) args mvars
    | _, _ => return ()

partial def canBottomUp (e : Expr) (mvar? : Option Expr := none) (fuel : Nat := 10) : MetaM Bool := do
  -- Here we check if `e` can be safely elaborated without its expected type.
  -- These are incomplete (and possibly unsound) heuristics.
  -- TODO: do I need to snapshot the state before calling this?
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if e.isFVar || e.isMVar || e.isNatLit || e.isStringLit then return true
    if getPPAnalyzeTrustOfNat (← getOptions) && e.isAppOfArity `OfNat.ofNat 3 then return true
    if getPPAnalyzeTrustOfScientific (← getOptions) && e.isAppOfArity `OfScientific.ofScientific 5 then return true
    let f := e.getAppFn
    if !f.isConst && !f.isFVar then return false
    let args := e.getAppArgs
    let fType ← replaceLPsWithVars (← inferType e.getAppFn)
    let ⟨mvars, bInfos, resultType⟩ ← forallMetaBoundedTelescope fType e.getAppArgs.size
    for i in [:mvars.size] do
      if bInfos[i] == BinderInfo.instImplicit then
        inspectOutParams args[i] mvars[i]
      else if bInfos[i] == BinderInfo.default then
        if ← canBottomUp args[i] mvars[i] fuel then tryUnify args[i] mvars[i]
    if ← (isHBinOp e <&&> (valUnknown mvars[0] <||> valUnknown mvars[1])) then tryUnify mvars[0] mvars[1]
    if mvar?.isSome then tryUnify resultType (← inferType mvar?.get!)
    let resultType ← instantiateMVars resultType
    return !resultType.hasMVar

def isHigherOrder (type : Expr) : MetaM Bool := do
  withTransparency TransparencyMode.all do forallTelescopeReducing type fun xs b => xs.size > 0 && b.isSort

def isFunLike (e : Expr) : MetaM Bool := do
  withTransparency TransparencyMode.all do forallTelescopeReducing (← inferType e) fun xs b => xs.size > 0

def isSubstLike (e : Expr) : Bool :=
  e.isAppOfArity `Eq.ndrec 6 || e.isAppOfArity `Eq.rec 6

def nameNotRoundtrippable (n : Name) : Bool :=
  n.hasMacroScopes || isPrivateName n || containsNum n
where
  containsNum
    | Name.str p .. => containsNum p
    | Name.num ..   => true
    | Name.anonymous => false

def mvarName (mvar : Expr) : MetaM Name := do
  (← getMVarDecl mvar.mvarId!).userName

def containsBadMax : Level → Bool
  | Level.succ u ..   => containsBadMax u
  | Level.max u v ..  => (u.hasParam && v.hasParam) || containsBadMax u || containsBadMax v
  | Level.imax u v .. => containsBadMax u || containsBadMax v
  | _                 => false

open SubExpr

structure Context where
  knowsType   : Bool
  knowsLevel  : Bool -- only constants look at this
  inBottomUp  : Bool := false
  parentIsApp : Bool := false
  deriving Inhabited, Repr

structure State where
  annotations : RBMap Pos Options compare := {}

abbrev AnalyzeM := ReaderT Context (ReaderT SubExpr (StateRefT State MetaM))

def withKnowing (knowsType knowsLevel : Bool) (x : AnalyzeM α) : AnalyzeM α := do
  withReader (fun ctx => { ctx with knowsType := knowsType, knowsLevel := knowsLevel }) x

builtin_initialize analyzeFailureId : InternalExceptionId ← registerInternalExceptionId `analyzeFailure

def checkKnowsType : AnalyzeM Unit := do
  if not (← read).knowsType then
    throw $ Exception.internal analyzeFailureId

def annotateBoolAt (n : Name) (pos : Pos) : AnalyzeM Unit := do
  let opts := (← get).annotations.findD pos {} |>.setBool n true
  trace[pp.analyze.annotate] "{pos} {n}"
  modify fun s => { s with annotations := s.annotations.insert pos opts }

def annotateBool (n : Name) : AnalyzeM Unit := do
  annotateBoolAt n (← getPos)

def annotateNamedArg (n : Name) (appPos : Pos) : AnalyzeM Bool := do
  if nameNotRoundtrippable n then
    trace[pp.analyze.annotate.badName] "{appPos} {n}"
    annotateBoolAt `pp.explicit appPos
    return false
  else
    annotateBool `pp.analysis.namedArg
    return true

partial def analyze (parentIsApp : Bool := false) : AnalyzeM Unit := do
  checkMaxHeartbeats "Delaborator.topDownAnalyze"
  trace[pp.analyze] "{(← read).knowsType}.{(← read).knowsLevel}"
  let e ← getExpr
  let opts ← getOptions

  if ← !e.isAtomic <&&> !(getPPProofs opts) <&&> (try Meta.isProof e catch ex => false) then
    if getPPProofsWithType opts then
      withType $ withKnowing true true $ analyze
    else pure ()
  else
    withReader (fun ctx => { ctx with parentIsApp := parentIsApp }) do
      match (← getExpr) with
      | Expr.app ..     => analyzeApp
      | Expr.forallE .. => analyzePi
      | Expr.lam ..     => analyzeLam
      | Expr.const ..   => analyzeConst
      | Expr.sort ..    => analyzeSort
      | Expr.proj ..    => analyzeProj
      | Expr.fvar ..    => analyzeFVar
      | Expr.mdata ..   => analyzeMData
      | Expr.letE ..    => analyzeLet
      | Expr.lit ..     => pure ()
      | Expr.mvar ..    => pure ()
      | Expr.bvar ..    => pure ()
where
  analyzeApp := do
    let couldBottomUp ← canBottomUp (← getExpr)
    withReader (fun ctx => { ctx with inBottomUp := ctx.inBottomUp || (!ctx.knowsType && couldBottomUp) }) do
      withKnowing true true $ analyzeAppStaged (← getExpr).getAppFn (← getExpr).getAppArgs

    if !(← read).knowsType then
      if !couldBottomUp then
        annotateBool `pp.analysis.needsType
        withType $ withKnowing true false $ analyze
      else
        -- structure instances will "seem" bottomUp-okay but may not be when
        -- pretty-printed as its fields.
        match (← getExpr).isConstructorApp? (← getEnv) with
        | none   => pure ()
        | some s =>
          if isStructure (← getEnv) s.induct then
            withType do
              annotateBool `pp.structureInstanceTypes
              withKnowing true false $ analyze

  analyzeAppStaged (f : Expr) (args : Array Expr) : AnalyzeM Unit := do
    let fType ← replaceLPsWithVars (← inferType f)
    let ⟨mvars, bInfos, resultType⟩ ← forallMetaBoundedTelescope fType args.size
    let rest := args.extract mvars.size args.size
    let args := args.shrink mvars.size

    -- Unify with the expected type
    tryUnify (← inferType (mkAppN f args)) resultType

    let mut bottomUps      := mkArray args.size false
    -- Collect explicit arguments that can be elaborated without expected type, with *no* top-down info
    -- Note: we perform this before the next pass because we prefer simple bottom-ups to unify first before
    -- more complex ones.
    for target in [fun _ => none, fun i => some mvars[i]] do
      for i in [:args.size] do
        if bInfos[i] == BinderInfo.default then
          -- allow bottom-up (and forbid `_`) as long as the value is unknown
          -- TODO: why not only if the type is unknown?
          if ← valUnknown mvars[i] <&&> canBottomUp args[i] (target i) then
            if ← typeUnknown mvars[i] then
              match args[i].isConstructorApp? (← getEnv) with
              | none   => pure ()
              | some s =>
                if isStructure (← getEnv) s.induct then
                  withNaryArg (f.getAppNumArgs + i) $ withType do
                    annotateBool `pp.structureInstanceTypes
                    withKnowing true false $ analyze
            tryUnify args[i] mvars[i]
            bottomUps := bottomUps.set! i true

    -- Next, look at out params
    for i in [:args.size] do
      if bInfos[i] == BinderInfo.instImplicit then
        inspectOutParams args[i] mvars[i]

    -- Collect implicit higher-order arguments
    let mut higherOrders := mkArray args.size false
    for i in [:args.size] do
      if not (← bInfos[i] == BinderInfo.implicit) then continue
      if not (← isHigherOrder (← inferType args[i])) then continue
      if getPPAnalyzeTrustId (← getOptions) && isIdLike args[i] then continue

      if getPPAnalyzeTrustKnownFOType2TypeHOFuns (← getOptions) && not (← valUnknown mvars[i])
        && (← isType2Type (args[i])) && (← isFOLike (args[i])) then continue

      tryUnify args[i] mvars[i]
      higherOrders := higherOrders.set! i true

    if ← (isHBinOp (← getExpr) <&&> (valUnknown mvars[0] <||> valUnknown mvars[1])) then tryUnify mvars[0] mvars[1]

    discard <| processPostponed (mayPostpone := true)

    let forceRegularApp : Bool :=
      (getPPAnalyzeTrustSubst (← getOptions) && isSubstLike (← getExpr))
      || (getPPAnalyzeTrustCoe (← getOptions) && isCoe (← getExpr))

    -- Now, if this is the first staging, analyze the n-ary function without expected type
    if !f.isApp then withKnowing false (forceRegularApp || !(← instantiateMVars fType).hasLevelMVar) $ withNaryFn (analyze (parentIsApp := true))

    let appPos ← getPos

    for i in [:args.size] do
      let arg := args[i]
      let argType ← inferType arg

      withNaryArg (f.getAppNumArgs + i) do
        withReader (fun ctx => { ctx with inBottomUp := ctx.inBottomUp || bottomUps[i] }) do
          match bInfos[i] with
          | BinderInfo.default =>
            if !(← valUnknown mvars[i]) && !(← read).inBottomUp && !(← isFunLike arg) then
              if ← checkpointDefEq mvars[i] arg then
                annotateBool `pp.analysis.hole

          | BinderInfo.implicit =>
            if (← valUnknown mvars[i] <||> higherOrders[i]) && !forceRegularApp then
              discard <| annotateNamedArg (← mvarName mvars[i]) appPos
            else
              annotateBool `pp.analysis.skip

          | BinderInfo.instImplicit =>
            -- Note: apparently checking valUnknown here is not sound, because the elaborator
            -- will not happily assign instImplicits that it cannot synthesize
            if getPPAnalyzeCheckInstances (← getOptions) then
              let instResult ← try trySynthInstance argType catch _ => LOption.undef
              match instResult with
              | LOption.some inst =>
                if ← checkpointDefEq inst arg then annotateBool `pp.analysis.skip
                else discard <| annotateNamedArg (← mvarName mvars[i]) appPos
              | _                 => discard <| annotateNamedArg (← mvarName mvars[i]) appPos
          | BinderInfo.auxDecl        => pure ()
          | BinderInfo.strictImplicit => unreachable!
          withKnowing (not (← typeUnknown mvars[i])) true analyze
          tryUnify mvars[i] args[i]

      if not rest.isEmpty then analyzeAppStaged (mkAppN f args) rest

  maybeAddExplicit : AnalyzeM Unit := do
    -- See `MonadLift.noConfusion for an example where this is necessary.
    if !(← read).parentIsApp then
      let type ← inferType (← getExpr)
      if type.isForall && type.bindingInfo! == BinderInfo.implicit then
        annotateBool `pp.analysis.needsExplicit

  analyzeConst : AnalyzeM Unit := do
    let Expr.const n ls .. ← getExpr | unreachable!
    if !(← read).knowsLevel && !ls.isEmpty then
      -- TODO: this is a very crude heuristic, motivated by https://github.com/leanprover/lean4/issues/590
      unless getPPAnalyzeOmitMax (← getOptions) && ls.any containsBadMax do
      annotateBool `pp.universes
    maybeAddExplicit

  analyzePi : AnalyzeM Unit := do
    annotateBool `pp.binderTypes
    withBindingDomain $ withKnowing true false analyze
    withBindingBody Name.anonymous analyze

  analyzeLam : AnalyzeM Unit := do
    if !(← read).knowsType then annotateBool `pp.binderTypes
    withBindingDomain $ withKnowing true false analyze
    withBindingBody Name.anonymous analyze

  analyzeLet : AnalyzeM Unit := do
    let Expr.letE n t v body .. ← getExpr | unreachable!
    if !(← canBottomUp v) then
      annotateBool `pp.analysis.letVarType
      withLetVarType $ withKnowing true false analyze
      withLetValue $ withKnowing true true analyze
    else
      withReader (fun ctx => { ctx with inBottomUp := true }) do
        withLetValue $ withKnowing true true analyze

    withLetBody analyze

  analyzeSort  : AnalyzeM Unit := pure ()
  analyzeProj  : AnalyzeM Unit := withProj analyze
  analyzeFVar  : AnalyzeM Unit := maybeAddExplicit
  analyzeMData : AnalyzeM Unit := withMDataExpr analyze

end TopDownAnalyze

open TopDownAnalyze SubExpr

def topDownAnalyze (e : Expr) : MetaM OptionsPerPos := do
  let s₀ ← get
  let uResult := (← getMCtx).levelMVarToParam e (alreadyUsedPred := fun _ => false) (paramNamePrefix := `_pp_analyze)
  setMCtx uResult.mctx
  let e := uResult.expr
  traceCtx `pp.analyze do
    withReader (fun ctx => { ctx with config := Lean.Elab.Term.setElabConfig ctx.config }) do
      let ϕ : AnalyzeM OptionsPerPos := do analyze; (← get).annotations
      try
        let knowsType := getPPAnalyzeKnowsType (← getOptions)
        ϕ { knowsType := knowsType, knowsLevel := knowsType } (mkRoot e) |>.run' {}
      catch ex =>
        trace[pp.analyze.error] "failed"
        pure {}
      finally set s₀

builtin_initialize
  registerTraceClass `pp.analyze
  registerTraceClass `pp.analyze.annotate
  registerTraceClass `pp.analyze.tryUnify
  registerTraceClass `pp.analyze.error

end Lean.PrettyPrinter.Delaborator
