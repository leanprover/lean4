/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis
import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow
import Lean.Meta.Tactic.Ext

/-!
This module contains the implementation of the pre processing pass for automatically splitting up
structures containing information about supported types into individual parts recursively.

The implementation operates on all "interesting" types where a type is interesting if it is a non
recursive structure and at least one of the following conditions hold:
- it contains something of type `BitVec`/`UIntX`/`IntX`/`Bool`
- it is parametrized by an interesting type
- it contains another interesting type

For these it:
1. Iterates over all variables in the local context that have an interesting type. For these it
   recursively asserts all of the contained hypotheses as local facts
2. It post-processes with a custom simp-set that:
   - runs `ext_iff` lemmas if available in order to handle equality on structures
   - runs simprocs to bubble applications of projections onto control flow operators such as `ite`
     or `cond` into the control flow
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

/--
Add simp lemmas that we want to apply to structures that we find interesting to `simprocs` and
`theorems`.
-/
public def addStructureSimpLemmas (simprocs : Simprocs) (theorems : SimpTheoremsArray) :
    PreProcessM (Simprocs × SimpTheoremsArray) := do
  let mut simprocs := simprocs
  let mut theorems := theorems
  let interesting := (← PreProcessM.getTypeAnalysis).interestingStructures
  let env ← getEnv
  for const in interesting do
    let constInfo ← getConstInfoInduct const
    if let some extIffThm ← findExtIff? constInfo then
      trace[Meta.Tactic.bv] m!"Using ext_iff: {extIffThm}"
      theorems ← theorems.addTheorem (.decl extIffThm) (mkConst extIffThm)
    let fields := (getStructureInfo env const).fieldNames.size
    let numParams := constInfo.numParams
    for proj in 0...fields do
      -- We use the simprocs with pre such that we push in projections eagerly in order to
      -- potentially not have to simplify complex structure expressions that we only project one
      -- element out of.
      let path := mkApplyProjControlDiscrPath const numParams proj ``ite 5
      simprocs := simprocs.addCore path ``applyIteSimproc false (.inl applyIteSimproc)
      let path := mkApplyProjControlDiscrPath const numParams proj ``cond 4
      simprocs := simprocs.addCore path ``applyCondSimproc false (.inl applyCondSimproc)
  return (simprocs, theorems)
where
  findExtIff? (info : InductiveVal) : MetaM (Option Name) := do
    let pat ← mkConstAppWithMVars info.name
    let thms ← Ext.getExtTheorems pat
    if thms.isEmpty then return none
    let .str root s := thms[0]!.declName | return none
    let extIffThm := .str root (s ++ "_iff")
    unless (← getEnv).contains extIffThm do return none
    return some extIffThm

  /--
  Constructs `declName ?m.1 ?m.2 ...` as a synthetic discr tree pattern for ext theorems associated
  with `declName`.
  -/
  mkConstAppWithMVars (declName : Name) : MetaM Expr := do
    let c ← mkConstWithFreshMVarLevels declName
    let (mvars, _, _) ← forallMetaTelescopeReducing (← inferType c)
    return mkAppN c mvars

public partial def structuresPass : Pass where
  name := `structures
  run' goal := do
    let interesting := (← PreProcessM.getTypeAnalysis).interestingStructures
    if interesting.isEmpty then return goal
    goal.withContext do
      let mut worklist := #[]
      for decl in ← getLCtx do
        if decl.isLet || decl.isImplementationDetail then
          continue
        let .const const us := decl.type.getAppFn | continue
        if interesting.contains const then
          worklist := worklist.push (mkFVar decl.fvarId, const, us, decl.type.getAppArgs)

      let mut newHyps : Array Hypothesis := #[]
      let env ← getEnv
      while h : 0 < worklist.size do
        let (value, structConst, us, params) := worklist.back
        worklist := worklist.pop
        let fields := (getStructureInfo env structConst).fieldNames.size
        let constInfo ← getConstInfoInduct structConst
        let ctorInfo ← getConstInfoCtor constInfo.ctors.head!
        for proj in 0...fields do
          let projValue ← mkProjFn ctorInfo us params proj value
          let projType ← inferType projValue
          if ← Meta.isProp projType then
            newHyps := newHyps.push {
              userName := `h
              type := projType
              value := projValue
            }
          else
            let .const const us := projType.getAppFn | continue
            if interesting.contains const then
              worklist := worklist.push (projValue, const, us, projType.getAppArgs)

      let (_, goal) ← goal.assertHypotheses newHyps
      postprocess goal
where
  postprocess (goal : MVarId) : PreProcessM (Option MVarId) := do
    goal.withContext do
      let mut simprocs : Simprocs := {}
      let mut relevantLemmas : SimpTheoremsArray := #[]
      (simprocs, relevantLemmas) ← addStructureSimpLemmas simprocs relevantLemmas
      relevantLemmas ← addDefaultTypeAnalysisLemmas relevantLemmas
      let cfg ← PreProcessM.getConfig
      let simpCtx ← Simp.mkContext
        (config := {
          failIfUnchanged := false,
          implicitDefEqProofs := false, -- leanprover/lean4/pull/7509
          maxSteps := cfg.maxSteps,
        })
        (simpTheorems := relevantLemmas)
        (congrTheorems := ← getSimpCongrTheorems)
      let ⟨result?, _⟩ ←
        simpGoal
          goal
          (ctx := simpCtx)
          (simprocs := #[simprocs])
          (fvarIdsToSimp := ← getPropHyps)
      let some (_, newGoal) := result? | return none
      return newGoal

end Normalize
end Lean.Meta.Tactic.BVDecide
