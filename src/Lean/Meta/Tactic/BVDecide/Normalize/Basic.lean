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

def Target.mvarId : Target → MVarId
  | .mvarIdTarget mvar => mvar
  | .grindTarget goal => goal.mvarId

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
The immutable context of the `bv_normalize` preprocessing pipeline.
-/
structure PreProcessContext where
  /--
  The configuration that the tactic was called with.
  -/
  config : BVDecideConfig
  /--
  The types that the structure and enum analysis is restricted to, as provided by the `types`
  clause. If this is `none` the analysis discovers the relevant types on its own.
  -/
  restrictedTypes : Option (Array Name) := none

structure PreProcessState where
  /--
  Cache for the `Simp` component of the rewriter.
  -/
  rewriteSimpCache : Sym.Simp.Cache := {}
  /--
  Cache for the `DSimp` component of the rewriter.
  -/
  rewriteDSimpCache : Sym.DSimp.Cache := {}
  /--
  Cache for the `Simp` component of the AC pass.
  -/
  acCache : Sym.Simp.Cache := {}
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
def getRestrictedTypes : PreProcessM (Option (Array Name)) := return (← read).restrictedTypes

@[inline]
def getTarget : PreProcessM Target := return (← get).target

@[inline]
def getTargetMVarId : PreProcessM MVarId := return (← get).target.mvarId

@[inline]
def setTarget (target : Target) : PreProcessM Unit :=
  modify fun s => { s with target := target }

@[inline]
def didChange : PreProcessM Bool := return (← get).didChange

@[inline]
def resetDidChange : PreProcessM Unit := modify fun s => { s with didChange := false }

@[inline]
def setDidChange : PreProcessM Unit := modify fun s => { s with didChange := true }

@[inline]
def takeRewriteSimpCache : PreProcessM Sym.Simp.Cache := do
  modifyGet fun s => (s.rewriteSimpCache, { s with rewriteSimpCache := {} })

@[inline]
def setRewriteSimpCache (cache : Sym.Simp.Cache) : PreProcessM Unit := do
  modify fun s => { s with rewriteSimpCache := cache }

@[inline]
def dropRewriteSimpCache : PreProcessM Unit := do
  discard <| takeRewriteSimpCache

@[inline]
def takeRewriteDSimpCache : PreProcessM Sym.DSimp.Cache := do
  modifyGet fun s => (s.rewriteDSimpCache, { s with rewriteDSimpCache := {} })

@[inline]
def setRewriteDSimpCache (cache : Sym.DSimp.Cache) : PreProcessM Unit := do
  modify fun s => { s with rewriteDSimpCache := cache }

@[inline]
def dropRewriteDSimpCache : PreProcessM Unit := do
  discard <| takeRewriteDSimpCache

@[inline]
def takeACCache : PreProcessM Sym.Simp.Cache := do
  modifyGet fun s => (s.acCache, { s with acCache := {} })

@[inline]
def setACCache (cache : Sym.Simp.Cache) : PreProcessM Unit := do
  modify fun s => { s with acCache := cache }

@[inline]
def dropACCache : PreProcessM Unit := do
  discard <| takeACCache

def dropFixpointCaches : PreProcessM Unit := do
  dropRewriteSimpCache
  dropRewriteDSimpCache
  dropACCache

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
  ReaderT.run x ctx |>.run' { target }

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
      (← PreProcessM.getTargetMVarId).assign newHyp.value
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
  PreProcessM.dropFixpointCaches
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
