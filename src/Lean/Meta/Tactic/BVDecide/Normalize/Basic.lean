/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Attr
public import Std.Tactic.BVDecide.Syntax
public import Lean.Meta.Sym.ExprPtr
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.InstantiateMVarsS
public import Lean.Meta.Sym.DSimp.DSimpM
import Lean.Meta.Sym.DSimp.Result
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.BVDecide.Types

public section

/-!
This module contains the basic preprocessing pipeline framework for `bv_normalize`.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

open Elab.Tactic.BVDecide (BVDecideConfig)


@[inline]
def withDoneResult {m : Type → Type} [Monad m] (x : m Sym.Simp.Result) : m Sym.Simp.Result := do
  let x ← x
  match x with
  | .rfl _ dep => return .rfl true dep
  | .step e' proof _ dep =>  return .step e' proof true dep

inductive Target where
  | mvarIdTarget (mvar : MVarId)
  | grindTarget (goal : Grind.Goal)
  deriving Inhabited

namespace Target

def mvarId : Target → MVarId
  | .mvarIdTarget mvar => mvar
  | .grindTarget goal => goal.mvarId

def isGrind : Target → Bool
  | .mvarIdTarget .. => false
  | .grindTarget .. => true

def isMVar : Target → Bool
  | .mvarIdTarget .. => true
  | .grindTarget .. => false

end Target

/--
The various kinds of matches supported by the match to cond infrastructure.
-/
inductive MatchKind
  /--
  It is a full match statement on an enum inductive with one constructor handled per arm.
  The ctors are listed in the order they occur in the match statement in `ctors`.
  -/
  | simpleEnum (info : InductiveVal) (ctors : Array ConstructorVal)
  /--
  It is a match statement on an enum inductive with a default arm, all explicitly handled ctors
  are listed in `ctors` in the order they occur in the match statement.
  -/
  | enumWithDefault (info : InductiveVal) (ctors : Array ConstructorVal)

/--
The enum inductive that the match discriminates on.
-/
def MatchKind.getEnumInfo : MatchKind → InductiveVal
  | .simpleEnum info .. | .enumWithDefault info .. => info

/--
Contains the result of the type analysis to be used in the structures and enums pass.
-/
structure TypeAnalysis where
  /--
  Structures that are interesting for the structures pass.
  -/
  interestingStructures : Std.HashSet Name := {}
  /--
  Inductives enums that are interesting for the enums pass.
  -/
  interestingEnums : Std.HashSet Name := {}
  /--
  `func.match_x` auxiliary declarations that we consider interesting.
  -/
  interestingMatchers : Std.HashMap Name MatchKind := {}
  /--
  Other types that we've seen that are not interesting, currently only used as a cache.
  -/
  uninteresting : Std.HashSet Name := {}

inductive HypSource where
  | lctx (fvar : FVarId)
  | enumDomain (n : Name)
  | structureProjection (e : Expr)
  | andFlattened (s : HypSource)
  | grind
  deriving Inhabited, Hashable, BEq

partial instance : ToMessageData HypSource where
  toMessageData s :=
    go s
where
  go (s : HypSource) : MessageData :=
    match s with
    | .lctx fvar => m!"assumption {mkFVar fvar}"
    | .enumDomain n => m!"enum domain size lemma for {n}"
    | .structureProjection e => m!"structure lemma projection: {e}"
    | .andFlattened s => m!"and flattening from {go (stripFlatten s)}"
    | .grind => m!"grind state"

  stripFlatten (s : HypSource) : HypSource :=
    match s with
    | .andFlattened s => stripFlatten s
    | _ => s

structure Hyp where
  name : Name
  type : Expr
  value : Expr
  source : HypSource
  deriving Inhabited

instance : BEq Hyp where
  beq lhs rhs := lhs.type == rhs.type

instance : Hashable Hyp where
  hash hyp := hash hyp.type

instance : ToMessageData Hyp where
  toMessageData hyp := toMessageData hyp.type

/--
The mode that the `bv_normalize` preprocessing pipeline runs in.
-/
inductive Mode where
  /--
  A regular run as part of `bv_decide` or a standalone `bv_normalize`. `restrictedTypes` are the
  types that the structure and enum analysis is restricted to, as provided by the `types` clause.
  If this is `none` the analysis discovers the relevant types on its own.
  -/
  | solve (restrictedTypes : Option (Array Name))
  /--
  A run as part of `bv_decide_push`. It merely prepares the caches of the passes for later runs of
  the pipeline on descendants of this goal and may thus only produce context independent
  information.
  -/
  | push

namespace Mode

def isPush : Mode → Bool
  | .push => true
  | .solve .. => false

def restrictedTypes : Mode → Option (Array Name)
  | .solve types => types
  | .push => none

/--
Disables the configuration options that `mode` cannot support. In `push` mode these are the options
that either depend on the context (e.g. enums, structures) or require a more clever incrementality
scheme (e.g. `embeddedConstraintSubst`, `andFlattening`).
-/
def adjustConfig (mode : Mode) (config : BVDecideConfig) : BVDecideConfig :=
  match mode with
  | .solve .. => config
  | .push =>
    { config with
      enums := false
      fixedInt := false
      structures := false
      embeddedConstraintSubst := false
      andFlattening := false }

end Mode

/--
The immutable context of the `bv_normalize` preprocessing pipeline. Use `PreProcessContext.new` to
create one.
-/
structure PreProcessContext where
  private mk ::
  /--
  The configuration that the tactic was called with, already adjusted for `mode`.
  -/
  config : BVDecideConfig
  /--
  The mode that the pipeline runs in.
  -/
  mode : Mode

/--
Creates the context for a run of the pipeline in `mode`, disabling all configuration options that
`mode` does not support.
-/
def PreProcessContext.new (mode : Mode) (config : BVDecideConfig) : PreProcessContext where
  config := mode.adjustConfig config
  mode := mode

/--
Identifies the `Sym.Simp` cache that a pass operates on.
-/
inductive SimpCacheId where
  | rewrite
  | ac

/--
Identifies the `Sym.DSimp` cache that a pass operates on.
-/
inductive DSimpCacheId where
  | rewrite
  | reduction

namespace SimpCacheId

def get : SimpCacheId → Grind.BVDecide.Caches → Sym.Simp.Cache
  | .rewrite, caches => caches.rewriteSimp
  | .ac, caches => caches.ac

def set : SimpCacheId → Sym.Simp.Cache → Grind.BVDecide.Caches → Grind.BVDecide.Caches
  | .rewrite, cache, caches => { caches with rewriteSimp := cache }
  | .ac, cache, caches => { caches with ac := cache }

end SimpCacheId

namespace DSimpCacheId

def get : DSimpCacheId → Grind.BVDecide.Caches → Sym.DSimp.Cache
  | .rewrite, caches => caches.rewriteDSimp
  | .reduction, caches => caches.reduction

def set : DSimpCacheId → Sym.DSimp.Cache → Grind.BVDecide.Caches → Grind.BVDecide.Caches
  | .rewrite, cache, caches => { caches with rewriteDSimp := cache }
  | .reduction, cache, caches => { caches with reduction := cache }

end DSimpCacheId

structure PreProcessState where
  /--
  The caches of the passes that maintain one.
  -/
  caches : Grind.BVDecide.Caches := {}
  /--
  Analysis results for the structure and enum pass if required.
  -/
  typeAnalysis : TypeAnalysis := {}
  /--
  The target we are operating on.
  -/
  target : Target
  /--
  The set of hypotheses we are operating on. These should be interpreted from withing the lctx of
  the goal. But they may not necessarily be fvars registered in the goal.
  -/
  hypotheses : Array Hyp := #[]
  /--
  A didChange flag for our fixpoint simplification loop.
  -/
  didChange : Bool := false

abbrev PreProcessM : Type → Type := ReaderT PreProcessContext StateRefT PreProcessState Grind.GrindM

namespace Hyp

def applySimpResult (hyp : Hyp) (result : Sym.Simp.Result) : Sym.SymM Hyp := do
  match result with
  | .rfl .. => return hyp
  | .step type' proof _ _ =>
    let u ← Sym.getLevel hyp.type
    let proof' := mkApp4 (mkConst ``Eq.mp [u]) hyp.type type' proof hyp.value
    return { hyp with type := type', value := proof' }

def applyDSimpResult (hyp : Hyp) (result : Sym.DSimp.Result) : Sym.SymM Hyp := do
  return { hyp with type := result.getResultExpr hyp.type }

end Hyp

namespace PreProcessM

@[inline]
def getConfig : PreProcessM BVDecideConfig := return (← read).config

@[inline]
def getRestrictedTypes : PreProcessM (Option (Array Name)) := return (← read).mode.restrictedTypes

@[inline]
def isPushMode : PreProcessM Bool := return (← read).mode.isPush

@[inline]
def getTarget : PreProcessM Target := return (← get).target

@[inline]
def getTargetMVarId : PreProcessM MVarId := return (← get).target.mvarId

@[inline]
def setTarget (target : Target) : PreProcessM Unit :=
  modify fun s => { s with target := target }

/--
Runs `x` on the target if it is a grind goal and writes the updated goal back. Returns `none` if the
target is a plain `MVarId`.
-/
@[inline]
def withGrindGoal (x : Grind.GoalM α) : PreProcessM (Option α) := do
  let .grindTarget goal ← getTarget | return none
  let (res, goal) ← Grind.GoalM.run goal x
  setTarget <| .grindTarget goal
  return some res

/--
Closes the target using `falseProof : False`. Grind targets are additionally marked as inconsistent
so that `grind` knows that there is nothing left to do for this goal.
-/
def closeTarget (falseProof : Expr) : PreProcessM Unit := do
  match ← getTarget with
  | .mvarIdTarget mvarId => mvarId.assignFalseProof falseProof
  | .grindTarget .. => discard <| withGrindGoal <| Grind.closeGoal falseProof

@[inline]
def didChange : PreProcessM Bool := return (← get).didChange

@[inline]
def resetDidChange : PreProcessM Unit := modify fun s => { s with didChange := false }

@[inline]
def setDidChange : PreProcessM Unit := modify fun s => { s with didChange := true }

@[inline]
def getCaches : PreProcessM Grind.BVDecide.Caches := return (← get).caches

@[inline]
def setCaches (caches : Grind.BVDecide.Caches) : PreProcessM Unit := do
  modify fun s => { s with caches }

/--
Drops the caches of all passes that maintain one. In `bv_decide_push` mode this is a no-op as the
caches are the very thing that we want to hand to the next invocation.
-/
def dropPassCaches : PreProcessM Unit := do
  if !(← isPushMode) then
    setCaches {}

@[inline]
def getTypeAnalysis : PreProcessM TypeAnalysis := do
  return (← get).typeAnalysis

@[inline]
def lookupInterestingStructure (n : Name) : PreProcessM (Option Bool) := do
  let s ← getTypeAnalysis
  if s.uninteresting.contains n then
    return some false
  else if s.interestingStructures.contains n then
    return some true
  else
    return none

@[inline]
def modifyTypeAnalysis (f : TypeAnalysis → TypeAnalysis) :
    PreProcessM Unit := do
  modify fun s => { s with typeAnalysis := f s.typeAnalysis }

@[inline]
def markInterestingStructure (n : Name) : PreProcessM Unit := do
  modifyTypeAnalysis (fun s => { s with interestingStructures := s.interestingStructures.insert n })

@[inline]
def markInterestingEnum (n : Name) : PreProcessM Unit := do
  modifyTypeAnalysis (fun s => { s with interestingEnums := s.interestingEnums.insert n })

@[inline]
def markInterestingMatcher (n : Name) (k : MatchKind) : PreProcessM Unit := do
  modifyTypeAnalysis (fun s => { s with interestingMatchers := s.interestingMatchers.insert n k })

@[inline]
def markUninterestingConst (n : Name) : PreProcessM Unit := do
  modifyTypeAnalysis (fun s => { s with uninteresting := s.uninteresting.insert n })

@[inline]
def run (ctx : PreProcessContext) (target : Target) (x : PreProcessM α) :
    Grind.GrindM (α × PreProcessState) := do
  ReaderT.run x ctx |>.run { target }

@[inline]
def run' (ctx : PreProcessContext) (target : Target) (x : PreProcessM α) : Grind.GrindM α := do
  Prod.fst <$> run ctx target x

@[inline]
def pushHyp (hyp : Hyp) : PreProcessM Unit := do
  trace[Meta.Tactic.bv] m!"Learned hypothesis: {hyp.type}"
  modify fun s => { s with hypotheses := s.hypotheses.push hyp }

@[inline]
def addHyps (hyps : Array Hyp) : PreProcessM Unit := do
  hyps.forM fun hyp => do
    trace[Meta.Tactic.bv] m!"Learned hypothesis: {hyp.type}"
  modify fun s => { s with hypotheses := s.hypotheses ++ hyps }

@[inline]
def getHyps : PreProcessM (Array Hyp) := do
  return (← get).hypotheses

@[inline]
def flatMapHyps [Monad m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadRef m]
    [MonadLiftT PreProcessM m] (f : Hyp → m (Array Hyp)) : m Unit := do
  let hyps ← getHyps
  modify (m := PreProcessM) fun s => { s with hypotheses := #[] }
  let hyps ← hyps.flatMapM fun hyp => do
    let res ← f hyp
    match h : res.size with
    | 1 =>
      let newHyp := res[0]
      if newHyp != hyp then
        trace[Meta.Tactic.bv] m!"{hyp.type}  ==>  {newHyp.type}"
        setDidChange
    | 0 | n + 2 =>
      res.forM fun newHyp => do trace[Meta.Tactic.bv] m!"{hyp.type}  ==>  {newHyp.type}"
      setDidChange
    return res
  modify (m := PreProcessM) fun s => { s with hypotheses := hyps }

@[inline]
def mapIdxHyps [Monad m] [MonadLiftT PreProcessM m] [MonadError m] [MonadMCtx m] [MonadTrace m]
    [MonadOptions m] [AddMessageContext m] [Sym.Internal.MonadShareCommon m]
    (f : Nat → Hyp → m Hyp) : m Bool := do
  let hyps ← getHyps
  let mut newHyps := Array.emptyWithCapacity hyps.size
  for h : idx in 0...hyps.size do
    let hyp := hyps[idx]
    let newHyp ← f idx hyp
    if newHyp.type.isFalse then
      PreProcessM.closeTarget newHyp.value
      return true
    else
      if hyp != newHyp then
        trace[Meta.Tactic.bv] m!"{hyp.type}  ==>  {newHyp.type}"
        setDidChange
      newHyps := newHyps.push newHyp
  modify (m := PreProcessM) fun s => { s with hypotheses := newHyps }
  return false

@[inline]
def mapHyps [Monad m] [MonadLiftT PreProcessM m] [MonadError m] [MonadMCtx m] [MonadTrace m]
    [MonadOptions m] [AddMessageContext m] [Sym.Internal.MonadShareCommon m] (f : Hyp → m Hyp) :
    m Bool := do
  mapIdxHyps (fun _ hyp => f hyp)

@[inline]
def forHyps [Monad m] [MonadLiftT PreProcessM m] [MonadError m] (f : Hyp → m Unit) :
    m Unit := do
  let hyps ← getHyps
  hyps.forM f

/--
Runs `Sym.Simp` on `hyp`, using the cache identified by `cacheId` and updating it in place.
-/
def simpHyp (cacheId : SimpCacheId) (methods : Sym.Simp.Methods) (config : Sym.Simp.Config)
    (hyp : Hyp) : PreProcessM Hyp := do
  let caches ← getCaches
  let simpState := { persistentCache := cacheId.get caches }
  setCaches <| cacheId.set {} caches
  let (res, s) ← Sym.Simp.SimpM.run (methods := methods) (config := config) (s := simpState) do
    Sym.Simp.simp hyp.type
  setCaches <| cacheId.set s.persistentCache (← getCaches)
  hyp.applySimpResult res

/--
Runs `Sym.DSimp` on `hyp`, using the cache identified by `cacheId` and updating it in place.
-/
def dsimpHyp (cacheId : DSimpCacheId) (methods : Sym.DSimp.Methods) (config : Sym.DSimp.Config)
    (hyp : Hyp) : PreProcessM Hyp := do
  let caches ← getCaches
  let dsimpState := { cache := cacheId.get caches }
  setCaches <| cacheId.set {} caches
  let (res, s) ← Sym.DSimp.DSimpM.run (methods := methods) (config := config) (s := dsimpState) do
    Sym.DSimp.dsimp hyp.type
  setCaches <| cacheId.set s.cache (← getCaches)
  hyp.applyDSimpResult res

@[inline]
def simpHyps (cacheId : SimpCacheId) (methods : Sym.Simp.Methods) (config : Sym.Simp.Config) :
    PreProcessM Bool :=
  mapHyps (simpHyp cacheId methods config)

@[inline]
def dsimpHyps (cacheId : DSimpCacheId) (methods : Sym.DSimp.Methods) (config : Sym.DSimp.Config) :
    PreProcessM Bool :=
  mapHyps (dsimpHyp cacheId methods config)

def mapSimpHyps (methods : Sym.Simp.Methods) (config : Sym.Simp.Config) : PreProcessM Bool :=
  go |>.run' {}
where
  go : StateRefT Sym.Simp.Cache PreProcessM Bool :=
    mapHyps fun hyp => do
      let simpState := { persistentCache := ← modifyGet fun s => (s, {})}
      let (res, s) ← Sym.Simp.SimpM.run (methods := methods) (config := config) (s := simpState) do
        Sym.Simp.simp hyp.type
      set s.persistentCache
      hyp.applySimpResult res

def mapDSimpHyps (methods : Sym.DSimp.Methods) (config : Sym.DSimp.Config) : PreProcessM Bool :=
  go |>.run' {}
where
  go : StateRefT Sym.DSimp.Cache PreProcessM Bool :=
    mapHyps fun hyp => do
      let dsimpState := { cache := ← modifyGet fun s => (s, {})}
      let (res, s) ← Sym.DSimp.DSimpM.run (methods := methods) (config := config) (s := dsimpState) do
        Sym.DSimp.dsimp hyp.type
      set s.cache
      hyp.applyDSimpResult res

end PreProcessM

/--
A pass in the normalization pipeline. It operates on the current set of hypotheses stored in the
`PreProcessM` monad. If it manages to find a way to close the associated goal it can indicate so by
returning `true`. Otherwise it should always return `false`.
-/
structure Pass where
  name : Name
  run' : PreProcessM Bool

namespace Pass

@[inline]
def run (pass : Pass) : PreProcessM Bool := do
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"Running pass: {pass.name}") do
    pass.run'

/--
Repeatedly run a list of `Pass` until they either close the goal or an iteration doesn't change
the goal anymore.
-/
partial def fixpointPipeline (passes : List Pass) : PreProcessM Bool := do
  let res ← go
  PreProcessM.dropPassCaches
  return res
where
  go : PreProcessM Bool := do
    checkSystem "bv_decide"
    PreProcessM.resetDidChange
    for pass in passes do
      if ← pass.run then
        trace[Meta.Tactic.bv] "Fixpoint iteration solved the goal"
        return true

    if ← PreProcessM.didChange then
      trace[Meta.Tactic.bv] m!"Rerunning pipeline"
      go
    else
      trace[Meta.Tactic.bv] "Pipeline reached a fixpoint"
      return false

end Pass

end Normalize
end Lean.Meta.Tactic.BVDecide
