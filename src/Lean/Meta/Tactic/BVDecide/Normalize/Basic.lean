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

public section

/-!
This module contains the basic preprocessing pipeline framework for `bv_normalize`.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

open Elab.Tactic.BVDecide (BVDecideConfig)

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

structure Hyp where
  name : Name
  -- TODO: make me an ExprPtr
  type : Expr
  -- TODO: make me an ExprPtr
  value : Expr
  deriving Inhabited, Hashable, BEq

structure PreProcessState where
  /--
  Contains `FVarId` that we already know are in `bv_normalize` simp normal form and thus don't
  need to be processed again when we visit the next time.
  -/
  rewriteCache : Std.HashSet FVarId := {}
  /--
  Contains `FVarId` that we already know have been run through the AC normal form and thus don't
  don't need to be processed again when we visit the next time.
  -/
  acNfCache : Std.HashSet FVarId := {}
  /--
  Analysis results for the structure and enum pass if required.
  -/
  typeAnalysis : TypeAnalysis := {}
  goal : MVarId
  hypotheses : Array Hyp := #[]
  didChange : Bool := false

abbrev PreProcessM : Type → Type := ReaderT BVDecideConfig <| StateRefT PreProcessState MetaM

namespace PreProcessM

@[inline]
def getConfig : PreProcessM BVDecideConfig := read

@[inline]
def getGoal : PreProcessM MVarId := return (← get).goal

@[inline]
def setGoal (g : MVarId) : PreProcessM Unit :=
  modify fun s => { s with goal := g, didChange := g != s.goal }

@[inline]
def didChange : PreProcessM Bool := return (← get).didChange

@[inline]
def resetDidChange : PreProcessM Unit := modify fun s => { s with didChange := false }

@[inline]
def setDidChange : PreProcessM Unit := modify fun s => { s with didChange := true }

@[inline]
def checkRewritten (fvar : FVarId) : PreProcessM Bool := do
  return (← get).rewriteCache.contains fvar

@[inline]
def checkAcNf (fvar : FVarId) : PreProcessM Bool := do
  return (← get).acNfCache.contains fvar

@[inline]
def rewriteFinished (fvar : FVarId) : PreProcessM Unit := do
  modify (fun s => { s with rewriteCache := s.rewriteCache.insert fvar })

@[inline]
def acNfFinished (fvar : FVarId) : PreProcessM Unit := do
  modify (fun s => { s with acNfCache := s.acNfCache.insert fvar })

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
def run (cfg : BVDecideConfig) (goal : MVarId) (x : PreProcessM α) : MetaM (α × PreProcessState) := do
  let hyps ← goal.withContext do getPropHyps
  ReaderT.run x cfg |>.run {
    rewriteCache := Std.HashSet.emptyWithCapacity hyps.size,
    acNfCache := Std.HashSet.emptyWithCapacity hyps.size,
    goal,
  }

@[inline]
def run' (cfg : BVDecideConfig) (goal : MVarId) (x : PreProcessM α) : MetaM α := do
  let hyps ← goal.withContext do getPropHyps
  ReaderT.run x cfg |>.run' {
    rewriteCache := Std.HashSet.emptyWithCapacity hyps.size,
    acNfCache := Std.HashSet.emptyWithCapacity hyps.size,
    goal,
  }

def collectHypsFromGoal : PreProcessM Unit := do
  setDidChange
  (← get).goal.withContext do
    let hyps ← (← getPropHyps).mapM fun fvarId => do
      return {
        name := ← fvarId.getUserName
        type := ← instantiateMVars (← fvarId.getType)
        value := mkFVar fvarId
      }
    modify fun s => { s with hypotheses := hyps }

@[inline]
def pushHyp (hyp : Hyp) : PreProcessM Unit := do
  trace[Meta.Tactic.bv] m!"Learned hypothesis: {hyp.type}"
  modify fun s => { s with hypotheses := s.hypotheses.push hyp }

@[inline]
def addHyps (hyps : Array Hyp) : PreProcessM Unit := do
  hyps.forM fun hyp => do trace[Meta.Tactic.bv] m!"Learned hypothesis: {hyp.type}"
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
def mapIdxHyps [Monad m] [MonadLiftT PreProcessM m] [MonadLiftT MetaM m] [MonadError m]
    [MonadMCtx m] [MonadTrace m] [MonadOptions m] [AddMessageContext m]
    (f : Nat → Hyp → m Hyp) : m Bool := do
  let hyps ← getHyps
  let mut newHyps := Array.emptyWithCapacity hyps.size
  for h : idx in 0...hyps.size do
    let hyp := hyps[idx]
    let newHyp ← f idx hyp
    if newHyp.type.isFalse then
      (← PreProcessM.getGoal).assign newHyp.value
      return true
    else
      if hyp != newHyp then
        trace[Meta.Tactic.bv] m!"{hyp.type}  ==>  {newHyp.type}"
        setDidChange
      newHyps := newHyps.push newHyp
  modify (m := PreProcessM) fun s => { s with hypotheses := newHyps }
  return false

@[inline]
def mapHyps [Monad m] [MonadLiftT PreProcessM m] [MonadLiftT MetaM m] [MonadError m]
    [MonadMCtx m] [MonadTrace m] [MonadOptions m] [AddMessageContext m]
    (f : Hyp → m Hyp) : m Bool := do
  mapIdxHyps (fun _ hyp => f hyp)

@[inline]
def forHyps [Monad m] [MonadLiftT PreProcessM m] [MonadLiftT MetaM m] [MonadError m]
    (f : Hyp → m Unit) : m Unit := do
  let hyps ← getHyps
  hyps.forM f

end PreProcessM

/--
A pass in the normalization pipeline. Takes the current goal and produces a refined one or closes
the goal fully, indicated by returning `none`.
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
  checkSystem "bv_decide"
  PreProcessM.resetDidChange
  for pass in passes do
    if ← pass.run then
      trace[Meta.Tactic.bv] "Fixpoint iteration solved the goal"
      return true

  if ← PreProcessM.didChange then
    trace[Meta.Tactic.bv] m!"Rerunning pipeline"
    fixpointPipeline passes
  else
    trace[Meta.Tactic.bv] "Pipeline reached a fixpoint"
    return false

end Pass

end Normalize
end Lean.Meta.Tactic.BVDecide
