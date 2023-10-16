/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean.Data.RBMap
import Lean.Meta.SynthInstance
import Lean.Util.FindMVar
import Lean.Util.FindLevelMVar
import Lean.Util.CollectLevelParams
import Lean.Util.ReplaceLevel
import Lean.PrettyPrinter.Delaborator.Options
import Lean.PrettyPrinter.Delaborator.SubExpr
import Lean.Elab.Config

/-!
The top-down analyzer is an optional preprocessor to the delaborator that aims
to determine the minimal annotations necessary to ensure that the delaborated
expression can be re-elaborated correctly. Currently, the top-down analyzer
is neither sound nor complete: there may be edge-cases in which the expression
can still not be re-elaborated correctly, and it may also add many annotations
that are not strictly necessary.
-/

namespace Lean
open Meta SubExpr

register_builtin_option pp.analyze : Bool := {
  defValue := false
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

-- TODO: this is an arbitrary special case of a more general principle.
register_builtin_option pp.analyze.trustSubtypeMk : Bool := {
  defValue := true
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) assume the implicit arguments of Subtype.mk can be inferred"
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

register_builtin_option pp.analyze.explicitHoles : Bool := {
  defValue := false
  group    := "pp.analyze"
  descr    := "(pretty printer analyzer) use `_` for explicit arguments that can be inferred"
}

def getPPAnalyze                            (o : Options) : Bool := o.get pp.analyze.name pp.analyze.defValue
def getPPAnalyzeCheckInstances              (o : Options) : Bool := o.get pp.analyze.checkInstances.name pp.analyze.checkInstances.defValue
def getPPAnalyzeTypeAscriptions             (o : Options) : Bool := o.get pp.analyze.typeAscriptions.name pp.analyze.typeAscriptions.defValue
def getPPAnalyzeTrustSubst                  (o : Options) : Bool := o.get pp.analyze.trustSubst.name pp.analyze.trustSubst.defValue
def getPPAnalyzeTrustOfNat                  (o : Options) : Bool := o.get pp.analyze.trustOfNat.name pp.analyze.trustOfNat.defValue
def getPPAnalyzeTrustOfScientific           (o : Options) : Bool := o.get pp.analyze.trustOfScientific.name pp.analyze.trustOfScientific.defValue
def getPPAnalyzeTrustId                     (o : Options) : Bool := o.get pp.analyze.trustId.name pp.analyze.trustId.defValue
def getPPAnalyzeTrustSubtypeMk              (o : Options) : Bool := o.get pp.analyze.trustSubtypeMk.name pp.analyze.trustSubtypeMk.defValue
def getPPAnalyzeTrustKnownFOType2TypeHOFuns (o : Options) : Bool := o.get pp.analyze.trustKnownFOType2TypeHOFuns.name pp.analyze.trustKnownFOType2TypeHOFuns.defValue
def getPPAnalyzeOmitMax                     (o : Options) : Bool := o.get pp.analyze.omitMax.name pp.analyze.omitMax.defValue
def getPPAnalyzeKnowsType                   (o : Options) : Bool := o.get pp.analyze.knowsType.name pp.analyze.knowsType.defValue
def getPPAnalyzeExplicitHoles               (o : Options) : Bool := o.get pp.analyze.explicitHoles.name pp.analyze.explicitHoles.defValue

def getPPAnalysisSkip            (o : Options) : Bool := o.get `pp.analysis.skip false
def getPPAnalysisHole            (o : Options) : Bool := o.get `pp.analysis.hole false
def getPPAnalysisNamedArg        (o : Options) : Bool := o.get `pp.analysis.namedArg false
def getPPAnalysisLetVarType      (o : Options) : Bool := o.get `pp.analysis.letVarType false
def getPPAnalysisNeedsType       (o : Options) : Bool := o.get `pp.analysis.needsType false
def getPPAnalysisBlockImplicit   (o : Options) : Bool := o.get `pp.analysis.blockImplicit false

namespace PrettyPrinter.Delaborator

def returnsPi (motive : Expr) : MetaM Bool := do
  lambdaTelescope motive fun _ b => return b.isForall

def isNonConstFun (motive : Expr) : MetaM Bool := do
  match motive with
  | Expr.lam _    _ b _ => isNonConstFun b
  | _ => return motive.hasLooseBVars

def isSimpleHOFun (motive : Expr) : MetaM Bool :=
  return not (← returnsPi motive) && not (← isNonConstFun motive)

def isType2Type (motive : Expr) : MetaM Bool := do
  match ← inferType motive with
  | Expr.forallE _ (Expr.sort ..) (Expr.sort ..) .. => return true
  | _ => return false

def isFOLike (motive : Expr) : MetaM Bool := do
  let f := motive.getAppFn
  return f.isFVar || f.isConst

def isIdLike (arg : Expr) : Bool :=
  -- TODO: allow `id` constant as well?
  match arg with
  | Expr.lam _ _ (Expr.bvar ..) .. => true
  | _ => false

def isStructureInstance (e : Expr) : MetaM Bool := do
  match e.isConstructorApp? (← getEnv) with
  | some s => return isStructure (← getEnv) s.induct
  | none   => return false

namespace TopDownAnalyze

partial def hasMVarAtCurrDepth (e : Expr) : MetaM Bool := do
  let mctx ← getMCtx
  return Option.isSome <| e.findMVar? fun mvarId =>
    match mctx.findDecl? mvarId with
    | some mdecl => mdecl.depth == mctx.depth
    | _ => false

partial def hasLevelMVarAtCurrDepth (e : Expr) : MetaM Bool := do
  let mctx ← getMCtx
  return Option.isSome <| e.findLevelMVar? fun mvarId =>
    mctx.findLevelDepth? mvarId == some mctx.depth

private def valUnknown (e : Expr) : MetaM Bool := do
  hasMVarAtCurrDepth (← instantiateMVars e)

private def typeUnknown (e : Expr) : MetaM Bool := do
  valUnknown (← inferType e)

def isHBinOp (e : Expr) : Bool := Id.run do
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
  if !e.hasLevelParam then return e
  let lps := collectLevelParams {} e |>.params
  let mut replaceMap : HashMap Name Level := {}
  for lp in lps do replaceMap := replaceMap.insert lp (← mkFreshLevelMVar)
  return e.replaceLevel fun
    | Level.param n .. => replaceMap.find! n
    | l => if !l.hasParam then some l else none

def isDefEqAssigning (t s : Expr) : MetaM Bool := do
  withReader (fun ctx => { ctx with config := { ctx.config with assignSyntheticOpaque := true }}) $
    Meta.isDefEq t s

def checkpointDefEq (t s : Expr) : MetaM Bool := do
  Meta.checkpointDefEq (mayPostpone := false) do
    isDefEqAssigning t s

def isHigherOrder (type : Expr) : MetaM Bool := do
  forallTelescopeReducing type fun xs b => return xs.size > 0 && b.isSort

def isFunLike (e : Expr) : MetaM Bool := do
  forallTelescopeReducing (← inferType e) fun xs _ => return xs.size > 0

def isSubstLike (e : Expr) : Bool :=
  e.isAppOfArity ``Eq.ndrec 6 || e.isAppOfArity ``Eq.rec 6

def nameNotRoundtrippable (n : Name) : Bool :=
  n.hasMacroScopes || isPrivateName n || containsNum n
where
  containsNum
    | Name.str p .. => containsNum p
    | Name.num ..   => true
    | Name.anonymous => false

def mvarName (mvar : Expr) : MetaM Name :=
  return (←  mvar.mvarId!.getDecl).userName

def containsBadMax : Level → Bool
  | Level.succ u ..   => containsBadMax u
  | Level.max u v ..  => (u.hasParam && v.hasParam) || containsBadMax u || containsBadMax v
  | Level.imax u v .. => (u.hasParam && v.hasParam) || containsBadMax u || containsBadMax v
  | _                 => false

open SubExpr

structure Context where
  knowsType   : Bool
  knowsLevel  : Bool -- only constants look at this
  inBottomUp  : Bool := false
  parentIsApp : Bool := false
  subExpr     : SubExpr
  deriving Inhabited

structure State where
  annotations : OptionsPerPos := {}
  postponed   : Array (Expr × Expr) := #[] -- not currently used

abbrev AnalyzeM := ReaderT Context (StateRefT State MetaM)

instance (priority := low) : MonadReaderOf SubExpr AnalyzeM where
  read := Context.subExpr <$> read

instance (priority := low) : MonadWithReaderOf SubExpr AnalyzeM where
  withReader f x := fun ctx => x { ctx with subExpr := f ctx.subExpr }

def tryUnify (e₁ e₂ : Expr) : AnalyzeM Unit := do
  try
    let r ← isDefEqAssigning e₁ e₂
    if !r then modify fun s => { s with postponed := s.postponed.push (e₁, e₂) }
    pure ()
  catch _ =>
    modify fun s => { s with postponed := s.postponed.push (e₁, e₂) }

partial def inspectOutParams (arg mvar : Expr) : AnalyzeM Unit := do
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
    | Expr.forallE _ fd fb _, Expr.forallE _ _  mb _ => do
      -- TODO: do I need to check (← okBottomUp? args[i] mvars[i] fuel).isSafe here?
      -- if so, I'll need to take a callback
      if fd.isOutParam then
        tryUnify (args[i]!) (mvars[i]!)
      inspectAux (fb.instantiate1 args[i]!) (mb.instantiate1 mvars[i]!) (i+1) args mvars
    | _, _ => return ()

partial def isTrivialBottomUp (e : Expr) : AnalyzeM Bool := do
  let opts ← getOptions
  return e.isFVar
         || e.isConst || e.isMVar || e.isNatLit || e.isStringLit || e.isSort
         || (getPPAnalyzeTrustOfNat opts && e.isAppOfArity ``OfNat.ofNat 3)
         || (getPPAnalyzeTrustOfScientific opts && e.isAppOfArity ``OfScientific.ofScientific 5)

partial def canBottomUp (e : Expr) (mvar? : Option Expr := none) (fuel : Nat := 10) : AnalyzeM Bool := do
  -- Here we check if `e` can be safely elaborated without its expected type.
  -- These are incomplete (and possibly unsound) heuristics.
  -- TODO: do I need to snapshot the state before calling this?
  match fuel with
  | 0 => return false
  | fuel + 1 =>
    if ← isTrivialBottomUp e then return true
    let f := e.getAppFn
    if !f.isConst && !f.isFVar then return false
    let args := e.getAppArgs
    let fType ← replaceLPsWithVars (← inferType e.getAppFn)
    let (mvars, bInfos, resultType) ← forallMetaBoundedTelescope fType e.getAppArgs.size
    for i in [:mvars.size] do
      if bInfos[i]! == BinderInfo.instImplicit then
        inspectOutParams args[i]! mvars[i]!
      else if bInfos[i]! == BinderInfo.default then
        if ← isTrivialBottomUp args[i]! then tryUnify args[i]! mvars[i]!
        else if ← typeUnknown mvars[i]! <&&> canBottomUp args[i]! (some mvars[i]!) fuel then tryUnify args[i]! mvars[i]!
    if ← (pure (isHBinOp e) <&&> (valUnknown mvars[0]! <||> valUnknown mvars[1]!)) then tryUnify mvars[0]! mvars[1]!
    if mvar?.isSome then tryUnify resultType (← inferType mvar?.get!)
    return !(← valUnknown resultType)

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

structure App.Context where
  f               : Expr
  fType           : Expr
  args            : Array Expr
  mvars           : Array Expr
  bInfos          : Array BinderInfo
  forceRegularApp : Bool

structure App.State where
  bottomUps       : Array Bool
  higherOrders    : Array Bool
  funBinders      : Array Bool
  provideds       : Array Bool
  namedArgs       : Array Name := #[]

abbrev AnalyzeAppM := ReaderT App.Context (StateT App.State AnalyzeM)

mutual

  partial def analyze (parentIsApp : Bool := false) : AnalyzeM Unit := do
    checkSystem "Delaborator.topDownAnalyze"
    trace[pp.analyze] "{(← read).knowsType}.{(← read).knowsLevel}"
    let e ← getExpr
    let opts ← getOptions
    if ← (pure !e.isAtomic) <&&> pure !(getPPProofs opts) <&&> (try Meta.isProof e catch _ => pure false) then
      if getPPProofsWithType opts then
        withType $ withKnowing true true $ analyze
      return ()
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
      let mut willKnowType := (← read).knowsType
      if !(← read).knowsType && !(← canBottomUp (← getExpr)) then
        annotateBool `pp.analysis.needsType
        withType $ withKnowing true false $ analyze
        willKnowType := true

      else if ← (pure !(← read).knowsType <||> pure (← read).inBottomUp) <&&> isStructureInstance (← getExpr) then
        withType do
          annotateBool `pp.structureInstanceTypes
          withKnowing true false $ analyze
        willKnowType := true

      withKnowing willKnowType true $ analyzeAppStaged (← getExpr).getAppFn (← getExpr).getAppArgs

    analyzeAppStaged (f : Expr) (args : Array Expr) : AnalyzeM Unit := do
      let fType ← replaceLPsWithVars (← inferType f)
      let (mvars, bInfos, resultType) ← forallMetaBoundedTelescope fType args.size
      let rest := args.extract mvars.size args.size
      let args := args.shrink mvars.size

      -- Unify with the expected type
      if (← read).knowsType then tryUnify (← inferType (mkAppN f args)) resultType

      let forceRegularApp : Bool :=
        (getPPAnalyzeTrustSubst (← getOptions) && isSubstLike (← getExpr))
        || (getPPAnalyzeTrustSubtypeMk (← getOptions) && (← getExpr).isAppOfArity ``Subtype.mk 4)

      analyzeAppStagedCore { f, fType, args, mvars, bInfos, forceRegularApp } |>.run' {
        bottomUps    := mkArray args.size false,
        higherOrders := mkArray args.size false,
        provideds    := mkArray args.size false,
        funBinders   := mkArray args.size false
      }

      if not rest.isEmpty then
        -- Note: this shouldn't happen for type-correct terms
        if !args.isEmpty then
          analyzeAppStaged (mkAppN f args) rest

    maybeAddBlockImplicit : AnalyzeM Unit := do
      -- See `MonadLift.noConfusion for an example where this is necessary.
      if !(← read).parentIsApp then
        let type ← inferType (← getExpr)
        if type.isForall && type.bindingInfo! == BinderInfo.implicit then
          annotateBool `pp.analysis.blockImplicit

    analyzeConst : AnalyzeM Unit := do
      let Expr.const _ ls .. ← getExpr | unreachable!
      if !(← read).knowsLevel && !ls.isEmpty then
        -- TODO: this is a very crude heuristic, motivated by https://github.com/leanprover/lean4/issues/590
        unless getPPAnalyzeOmitMax (← getOptions) && ls.any containsBadMax do
        annotateBool `pp.universes
      maybeAddBlockImplicit

    analyzePi : AnalyzeM Unit := do
      withBindingDomain $ withKnowing true false analyze
      withBindingBody Name.anonymous analyze

    analyzeLam : AnalyzeM Unit := do
      if !(← read).knowsType then annotateBool `pp.funBinderTypes
      withBindingDomain $ withKnowing true false analyze
      withBindingBody Name.anonymous analyze

    analyzeLet : AnalyzeM Unit := do
      let Expr.letE _ _ v _    .. ← getExpr | unreachable!
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
    analyzeFVar  : AnalyzeM Unit := maybeAddBlockImplicit
    analyzeMData : AnalyzeM Unit := withMDataExpr analyze

  partial def analyzeAppStagedCore : AnalyzeAppM Unit := do
    collectBottomUps
    checkOutParams
    collectHigherOrders
    hBinOpHeuristic
    collectTrivialBottomUps
    discard <| processPostponed (mayPostpone := true)
    applyFunBinderHeuristic
    analyzeFn
    for i in [:(← read).args.size] do analyzeArg i
    maybeSetExplicit

  where
    collectBottomUps := do
      let { args, mvars, bInfos, ..} ← read
      for target in [fun _ => none, fun i => some mvars[i]!] do
        for i in [:args.size] do
          if bInfos[i]! == BinderInfo.default then
            if ← typeUnknown mvars[i]! <&&> canBottomUp args[i]! (target i) then
              tryUnify args[i]! mvars[i]!
              modify fun s => { s with bottomUps := s.bottomUps.set! i true }

    checkOutParams := do
      let { args, mvars, bInfos, ..} ← read
      for i in [:args.size] do
        if bInfos[i]! == BinderInfo.instImplicit then inspectOutParams args[i]! mvars[i]!

    collectHigherOrders := do
      let { args, mvars, bInfos, ..} ← read
      for i in [:args.size] do
        if not (bInfos[i]! == BinderInfo.implicit || bInfos[i]! == BinderInfo.strictImplicit) then continue
        if not (← isHigherOrder (← inferType args[i]!)) then continue
        if getPPAnalyzeTrustId (← getOptions) && isIdLike args[i]! then continue

        if getPPAnalyzeTrustKnownFOType2TypeHOFuns (← getOptions) && not (← valUnknown mvars[i]!)
          && (← isType2Type (args[i]!)) && (← isFOLike (args[i]!)) then continue

        tryUnify args[i]! mvars[i]!
        modify fun s => { s with higherOrders := s.higherOrders.set! i true }

    hBinOpHeuristic := do
      let { mvars, ..} ← read
      if ← (pure (isHBinOp (← getExpr)) <&&> (valUnknown mvars[0]! <||> valUnknown mvars[1]!)) then
        tryUnify mvars[0]! mvars[1]!

    collectTrivialBottomUps := do
      -- motivation: prevent levels from printing in
      -- Boo.mk : {α : Type u_1} → {β : Type u_2} → α → β → Boo.{u_1, u_2} α β
      let { args, mvars, bInfos, ..} ← read
      for i in [:args.size] do
        if bInfos[i]! == BinderInfo.default then
          if ← valUnknown mvars[i]! <&&> isTrivialBottomUp args[i]! then
            tryUnify args[i]! mvars[i]!
            modify fun s => { s with bottomUps := s.bottomUps.set! i true }

    applyFunBinderHeuristic := do
      let { args, mvars, bInfos, .. } ← read

      let rec core (argIdx : Nat) (mvarType : Expr) : AnalyzeAppM Bool := do
        match ← getExpr, mvarType with
        | Expr.lam .., Expr.forallE _ t b .. =>
          let mut annotated := false
          for i in [:argIdx] do
            if ← pure (bInfos[i]! == BinderInfo.implicit) <&&> valUnknown mvars[i]! <&&> withNewMCtxDepth (checkpointDefEq t mvars[i]!) then
              annotateBool `pp.funBinderTypes
              tryUnify args[i]! mvars[i]!
              -- Note: currently we always analyze the lambda binding domains in `analyzeLam`
              -- (so we don't need to analyze it again here)
              annotated := true
              break
          let annotatedBody ← withBindingBody Name.anonymous (core argIdx b)
          return annotated || annotatedBody

        | _, _ => return false

      for i in [:args.size] do
        if bInfos[i]! == BinderInfo.default then
          let b ← withNaryArg i (core i (← inferType mvars[i]!))
          if b then modify fun s => { s with funBinders := s.funBinders.set! i true }

    analyzeFn := do
      -- Now, if this is the first staging, analyze the n-ary function without expected type
      let {f, fType, forceRegularApp ..} ← read
      if !f.isApp then withKnowing false (forceRegularApp || !(← hasLevelMVarAtCurrDepth (← instantiateMVars fType))) $ withNaryFn (analyze (parentIsApp := true))

    annotateNamedArg (n : Name) : AnalyzeAppM Unit := do
      annotateBool `pp.analysis.namedArg
      modify fun s => { s with namedArgs := s.namedArgs.push n }

    analyzeArg (i : Nat) := do
      let { f, args, mvars, bInfos, forceRegularApp ..} ← read
      let { bottomUps, higherOrders, funBinders, ..} ← get
      let arg := args[i]!
      let argType ← inferType arg

      let processNaturalImplicit : AnalyzeAppM Unit := do
        if (← valUnknown mvars[i]! <||> pure higherOrders[i]!) && !forceRegularApp then
          annotateNamedArg (← mvarName mvars[i]!)
          modify fun s => { s with provideds := s.provideds.set! i true }
        else
          annotateBool `pp.analysis.skip

      withNaryArg (f.getAppNumArgs + i) do
        withTheReader Context (fun ctx => { ctx with inBottomUp := ctx.inBottomUp || bottomUps[i]! }) do

          match bInfos[i]! with
          | BinderInfo.default =>
            if ← pure (getPPAnalyzeExplicitHoles (← getOptions)) <&&> pure !(← valUnknown mvars[i]!) <&&> pure !(← readThe Context).inBottomUp <&&> pure !(← isFunLike arg) <&&> pure !funBinders[i]! <&&> checkpointDefEq mvars[i]! arg then
              annotateBool `pp.analysis.hole
            else
              modify fun s => { s with provideds := s.provideds.set! i true }

          | BinderInfo.implicit => processNaturalImplicit
          | BinderInfo.strictImplicit => processNaturalImplicit

          | BinderInfo.instImplicit =>
            -- Note: apparently checking valUnknown here is not sound, because the elaborator
            -- will not happily assign instImplicits that it cannot synthesize
            let mut provided := true
            if !getPPInstances (← getOptions) then
              annotateBool `pp.analysis.skip
              provided := false
            else if getPPAnalyzeCheckInstances (← getOptions) then
              let instResult ← try trySynthInstance argType catch _ => pure LOption.undef
              match instResult with
              | LOption.some inst =>
                if ← checkpointDefEq inst arg then annotateBool `pp.analysis.skip; provided := false
                else annotateNamedArg (← mvarName mvars[i]!)
              | _                 => annotateNamedArg (← mvarName mvars[i]!)
            else annotateBool `pp.analysis.skip; provided := false
            modify fun s => { s with provideds := s.provideds.set! i provided }
          if (← get).provideds[i]! then withKnowing (not (← typeUnknown mvars[i]!)) true analyze
          tryUnify mvars[i]! args[i]!

    maybeSetExplicit := do
      let { f, args, bInfos, ..} ← read
      if (← get).namedArgs.any nameNotRoundtrippable then
        annotateBool `pp.explicit
        for i in [:args.size] do
          if !(← get).provideds[i]! then
            withNaryArg (f.getAppNumArgs + i) do annotateBool `pp.analysis.hole
          if bInfos[i]! == BinderInfo.instImplicit && getPPInstanceTypes (← getOptions) then
            withType (withKnowing true false analyze)

end

end TopDownAnalyze

open TopDownAnalyze SubExpr

def topDownAnalyze (e : Expr) : MetaM OptionsPerPos := do
  let s₀ ← get
  withTraceNode `pp.analyze (fun _ => return e) do
    withReader (fun ctx => { ctx with config := Elab.Term.setElabConfig ctx.config }) do
      let ϕ : AnalyzeM OptionsPerPos := do withNewMCtxDepth analyze; pure (← get).annotations
      try
        let knowsType := getPPAnalyzeKnowsType (← getOptions)
        ϕ { knowsType := knowsType, knowsLevel := knowsType, subExpr := mkRoot e }
          |>.run' { : TopDownAnalyze.State }
      catch e =>
        trace[pp.analyze.error] "failed {e.toMessageData}"
        pure {}
      finally set s₀

builtin_initialize
  registerTraceClass `pp.analyze
  registerTraceClass `pp.analyze.annotate (inherited := true)
  registerTraceClass `pp.analyze.tryUnify (inherited := true)
  registerTraceClass `pp.analyze.error (inherited := true)

end Lean.PrettyPrinter.Delaborator
