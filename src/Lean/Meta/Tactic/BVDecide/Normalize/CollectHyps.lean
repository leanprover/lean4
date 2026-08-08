/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.LitValues

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

abbrev CollectM := StateRefT State Grind.GoalM

@[inline]
def recordHyp (hyp : Hyp) : CollectM Unit := do
  modify fun s => { s with hyps := s.hyps.push hyp }

def collectGoalHyps : Grind.GoalM (Array Hyp) := do
  let (_, res) ← go |>.run {}
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
    let eqcs ← Grind.getEqcs
    for eqc in eqcs do
      if let some representative ← analyzeClass eqc then
        let root ← Grind.getRootENode eqc.head!
        let homogeneous := !root.heqProofs
        for e in eqc do
          if e == representative then continue
          unless homogeneous do
            unless (← Grind.hasSameType e representative) do continue
          recordHyp {
            name := .anonymous
            type := ← Sym.share (← mkEq e representative),
            value := ← Grind.mkEqProof e representative,
            source := .grind
          }

  analyzeClass (eqc : List Expr) : CollectM (Option Expr) := do
    let elem := eqc.head!
    let root := (← Grind.getRootENode elem).self
    let type ← Sym.inferType elem
    match_expr type with
    | Bool =>
      if ← Grind.isEqBoolTrue elem then
        return some (← Sym.getBoolTrueExpr)
      else if ← Grind.isEqBoolFalse elem then
        return some (← Sym.getBoolFalseExpr)
      else
        return some root
    | BitVec w =>
      unless (Sym.getNatValue? w).isSome do return none
      handleEqcWithConstType eqc root Sym.getBitVecValue?
    | UInt8 => handleEqcWithConstType eqc root Sym.getUInt8Value?
    | UInt16 => handleEqcWithConstType eqc root Sym.getUInt16Value?
    | UInt32 => handleEqcWithConstType eqc root Sym.getUInt32Value?
    | UInt64 => handleEqcWithConstType eqc root Sym.getUInt64Value?
    | Int8 => handleEqcWithConstType eqc root Sym.getInt8Value?
    | Int16 => handleEqcWithConstType eqc root Sym.getInt16Value?
    | Int32 => handleEqcWithConstType eqc root Sym.getInt32Value?
    | Int64 => handleEqcWithConstType eqc root Sym.getInt64Value?
    -- Hack: Use UInt64/Int64 as the format is the same as USize/ISize but at the same time we don't
    -- care about the precise value for our purposes.
    | USize => handleEqcWithConstType eqc root Sym.getUInt64Value?
    | ISize => handleEqcWithConstType eqc root Sym.getInt64Value?
    | _ =>
      let some (const, _) := type.getAppFn'.const? | return none
      unless ← isPotentialTypeAnalysisType const do return none
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
  handleEqcWithConstType {α : Type} (eqc : List Expr) (default : Expr) (getConst : Expr → Option α)
      : CollectM (Option Expr) :=
    if let some constant := eqc.find? (getConst · |>.isSome) then
      return some constant
    else
      return some default
  

public def PreProcessM.collectTargetHyps : PreProcessM Unit := do
  let target ← PreProcessM.getTarget
  let hypotheses ←
    match target with
    | .mvarIdTarget g =>
      g.withContext do
        (← getPropHyps).mapM fun fvarId => do
          return {
            name := ← fvarId.getUserName
            type := ← Sym.instantiateMVarsS (← fvarId.getType)
            value := mkFVar fvarId
            source := .lctx fvarId
          }
    | .grindTarget g =>
      let (hypotheses, _) ← Grind.GoalM.run g collectGoalHyps
      pure hypotheses
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"Collected initial hypotheses") do
    hypotheses.forM fun hyp => do trace[Meta.Tactic.bv] m!"{hyp}"
  modify fun s => { s with hypotheses := hypotheses }

end Normalize
end Lean.Meta.Tactic.BVDecide
