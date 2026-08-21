/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
import Lean.Elab.Tactic.FalseOrByContra
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.LitValues
import Lean.Meta.Sym.Util
import Lean.Meta.Sym.Grind
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Sym.Intro
import Lean.Meta.Tactic.Grind.Simp

/-!
This module is responsible for collecting the hypotheses out of the target that `bv_decide` was told
to operate on.
- For regular `MVarId`-based targets it just collects everything from the local context.
- For grind's `Goal`-based targets it inspects the equivalence classes, in particular:
  - All members of `True` and `False` are collected as `h : p` and `h : ¬ p` respectively
  - For members of `Bool`, `BitVec const` and type analysis relevant eqcs it chooses a
    representative `r` and then collects the hypotheses `h₁ : e₁ = r`, ..., `hₙ : eₙ = r`.
    We try to choose an as-constant-as-possible representative to boost constant propagation and
    simplification in all of these hypotheses.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

structure State where
  hyps : Array Hyp := #[]

open Elab.Tactic.BVDecide in
abbrev CollectM := ReaderT BVDecideConfig StateRefT State Grind.GoalM

@[inline]
def recordHyp (hyp : Hyp) : CollectM Unit := do
  modify fun s => { s with hyps := s.hyps.push hyp }

@[inline]
def withFixedInt (x : CollectM (Option α)) : CollectM (Option α) := do
  if (← read).fixedInt then
    x
  else
    return none

open Elab.Tactic.BVDecide in
def collectGoalHyps (cfg : BVDecideConfig) : Grind.GoalM (Array Hyp) := do
  let (_, res) ← go |>.run cfg |>.run {}
  return res.hyps
where
  go : CollectM Unit := do
    collectTrue
    collectFalse
    collectRelevantEqualities
    collectNumBits

  /--
  Collect all true propositions. Notably equalities are not part of these.
  -/
  collectTrue : CollectM Unit := do
    let trueExpr ← Sym.getTrueExpr
    let trueEqc ← Grind.getEqc trueExpr
    for prop in trueEqc do
      if prop == trueExpr then
        continue
      recordHyp {
        name := .anonymous
        type := prop
        value := ← mkOfEqTrue (← Grind.mkEqTrueProof prop)
        source := .grind
      }

  /--
  Collect all false propositions.
  -/
  collectFalse : CollectM Unit := do
    let falseExpr ← Sym.getFalseExpr
    let falseEqc ← Grind.getEqc falseExpr
    for prop in falseEqc do
      if prop == falseExpr then
        continue
      recordHyp {
        name := .anonymous
        type := ← Sym.share <| mkNot prop
        value := ← mkOfEqFalse (← Grind.mkEqFalseProof prop)
        source := .grind
      }

  /--
  Collect equalities for all types that we consider relevant.
  -/
  collectRelevantEqualities : CollectM Unit := do
    for root in ← Grind.getExprs do
      let node ← Grind.getENode root
      unless node.isRoot do continue
      if let some representative ← analyzeClass root then
        let homogeneous := !node.heqProofs
        let eqc ← Grind.getEqc root
        for e in eqc do
          if e == representative then continue
          unless homogeneous do
            unless ← Grind.hasSameType e representative do continue
          recordHyp {
            name := .anonymous
            type := ← Sym.share (← mkEq e representative),
            value := ← Grind.mkEqProof e representative,
            source := .grind
          }

  analyzeClass (root : Expr) : CollectM (Option Expr) := do
    let type ← Sym.inferType root
    match_expr type with
    | Bool =>
      if ← Grind.isEqBoolTrue root then
        return some (← Sym.getBoolTrueExpr)
      else if ← Grind.isEqBoolFalse root then
        return some (← Sym.getBoolFalseExpr)
      else
        return some root
    | BitVec w =>
      unless (Sym.getNatValue? w).isSome do return none
      handleEqcWithConstType root Sym.getBitVecValue?
    | UInt8 => withFixedInt <| handleEqcWithConstType root Sym.getUInt8Value?
    | UInt16 => withFixedInt <| handleEqcWithConstType root Sym.getUInt16Value?
    | UInt32 => withFixedInt <| handleEqcWithConstType root Sym.getUInt32Value?
    | UInt64 => withFixedInt <| handleEqcWithConstType root Sym.getUInt64Value?
    | Int8 => withFixedInt <| handleEqcWithConstType root Sym.getInt8Value?
    | Int16 => withFixedInt <| handleEqcWithConstType root Sym.getInt16Value?
    | Int32 => withFixedInt <| handleEqcWithConstType root Sym.getInt32Value?
    | Int64 => withFixedInt <| handleEqcWithConstType root Sym.getInt64Value?
    -- Hack: Use UInt64/Int64 as the format is the same as USize/ISize but at the same time we don't
    -- care about the precise value for our purposes.
    | USize => withFixedInt <| handleEqcWithConstType root Sym.getUInt64Value?
    | ISize => withFixedInt <| handleEqcWithConstType root Sym.getInt64Value?
    | _ =>
      let some (const, _) := type.getAppFn'.const? | return none
      unless ← isPotentialTypeAnalysisType (← read) const do return none
      let eqc ← Grind.getEqc root
      if let some ctorApp ← eqc.findM? (liftM ∘ Meta.isConstructorApp) then
        return some ctorApp
      else
        return some root

  /--
  For USize/ISize we check if numBits is equivalent to some constant and if it is record that
  assumption.
  -/
  collectNumBits : CollectM Unit := do
    let numBits ← Sym.share <| mkConst ``System.Platform.numBits
    let eqc ← Grind.getEqc numBits
    if eqc.isEmpty then return ()
    if let some constant := eqc.find? (Sym.getNatValue? · |>.isSome) then
      recordHyp {
        name := .anonymous
        type := ← Sym.share (← mkEq numBits constant),
        value := ← Grind.mkEqProof numBits constant,
        source := .grind
      }

  /--
  Heuristic for choosing a canonical representative for a class: If the class contains a constant we
  choose the constant as representative, otherwise just a default value.
  -/
  handleEqcWithConstType {α : Type} (default : Expr) (getConst : Expr → Option α)
      : CollectM (Option Expr) := do
    let eqc ← Grind.getEqc default
    if let some constant := eqc.find? (getConst · |>.isSome) then
      return some constant
    else
      return some default

def recordLocalHyp (fvarId : FVarId) : Sym.SymM Hyp := do
  return {
    name := ← fvarId.getUserName
    type := ← Sym.instantiateMVarsS (← fvarId.getType)
    value := mkFVar fvarId
    source := .lctx fvarId
  }

def symByContradiction (goal : MVarId) : Sym.SymM (Array FVarId × MVarId) := do
  let (fvarIds, goal) ←
    match ← Sym.intros goal with
    | .goal fvarIds goal => pure (fvarIds, goal)
    | .failed => pure (#[], goal)
  goal.withContext do
    let goalType ← goal.getType
    unless ← isProp goalType do
      let goal ← goal.exfalso
      let goal ← Sym.preprocessMVar goal
      return (fvarIds, goal)
    if goalType.isFalse then
      return (fvarIds, goal)
    let some goal ← goal.byContra? | unreachable!
    let goal ← Sym.preprocessMVar goal
    let .goal contraFVarIds goal ← Sym.introN goal 1
      | throwError "`bv_decide` failed to introduce the negated goal"
    return (fvarIds ++ contraFVarIds, goal)

/--
Runs `intros; by_contra` on a `grind` goal. This does maintain maximal sharing but does *not*
internalize them into the e-graph. The rationale for this is that if the user wanted bv_decide to be
aware of e-graph information related to the goal they should run `by_contra` themselves in order to
force internalization. Otherwise `bv_decide` will only use existing e-graph information + the
bitvector information about the goal. This allows us to avoid internalizing huge bitvector
expressions that can just be attacked by `bv_decide` on its own.
-/
def setupGrindTarget (goal : Grind.Goal) : Grind.GrindM (Array FVarId × Grind.Goal) := do
  let (fvarIds, mvarId) ← symByContradiction goal.mvarId
  return (fvarIds, { goal with mvarId })

def setupTarget : PreProcessM (Option (Array Hyp)) := do
  match ← PreProcessM.getTarget with
  | .mvarIdTarget g =>
    let (_, g) ← symByContradiction g
    let g ← Sym.preprocessMVar g
    PreProcessM.setTarget <| .mvarIdTarget g
    g.withContext do
      return some <| ← (← getPropHyps).mapM fun fvarId =>
        return {
          name := ← fvarId.getUserName
          type := ← Sym.instantiateMVarsS (← fvarId.getType)
          value := mkFVar fvarId
          source := .lctx fvarId
        }
  | .grindTarget g =>
    let isPush ← PreProcessM.isPushMode
    let (introduced, g) ← if isPush then pure (#[], g) else setupGrindTarget g
    if g.inconsistent then return none
    let cfg ← PreProcessM.getConfig
    let (hyps, g) ← Grind.GoalM.run g do
      let hypotheses ← collectGoalHyps cfg
      let introduced : Array Hyp ← introduced.filterMapM fun fvarId => do
        unless ← isProp (← fvarId.getType) do return none
        return some {
          name := ← fvarId.getUserName
          type := ← Grind.preprocessLight (← fvarId.getType)
          value := mkFVar fvarId
          source := .lctx fvarId
        }
      return hypotheses ++ introduced
    PreProcessM.setTarget <| .grindTarget g
    return hyps

/--
Collects the hypotheses that `bv_decide` operates on.
-/
public def PreProcessM.collectTargetHyps : PreProcessM Bool := do
  let some hypotheses ← setupTarget | return true
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"Collected initial hypotheses") do
    hypotheses.forM fun hyp => do trace[Meta.Tactic.bv] m!"{hyp}"
  modify fun s => { s with hypotheses := hypotheses }
  return false

end Normalize
end Lean.Meta.Tactic.BVDecide
