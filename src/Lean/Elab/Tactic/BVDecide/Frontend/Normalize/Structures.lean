/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Simp
import Lean.Meta.Injective

/-!
This module contains the implementation of the pre processing pass for automatically splitting up
structures containing information about supported types into individual parts recursively.

The implementation runs cases recursively on all "interesting" types where a type is interesting if
it is a non recursive structure and at least one of the following conditions hold:
- it contains something of type `BitVec`/`UIntX`/`Bool`
- it is parametrized by an interesting type
- it contains another interesting type
Afterwards we also:
- apply relevant `injEq` theorems to support at least equality for these types out of the box.
- push projections of relevant types inside of `ite` and `cond`.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta


def applyIteSimproc : Simp.Simproc := fun e => do
  let proj := e.getAppFn
  let args := e.getAppArgs
  if h : args.size ≠ 0 then
    let_expr ite α c instDec t e := args.back | return .continue
    let params := args.pop
    let projApp := mkAppN proj params
    let newT := mkApp projApp t
    let newE := mkApp projApp e
    let newIf ← mkAppOptM ``ite #[none, c, instDec, newT, newE]
    let proof ← mkAppOptM ``apply_ite #[α, none, projApp, c, instDec, t, e]
    return .visit { expr := newIf, proof? := some proof }
  else
    return .continue

def applyCondSimproc : Simp.Simproc := fun e => do
  let proj := e.getAppFn
  let args := e.getAppArgs
  if h : args.size ≠ 0 then
    let_expr cond α c t e := args.back | return .continue
    let params := args.pop
    let projApp := mkAppN proj params
    let newT := mkApp projApp t
    let newE := mkApp projApp e
    let newCond ← mkAppOptM ``cond #[none, c, newT, newE]
    let proof ← mkAppOptM ``Bool.apply_cond #[α, none, projApp, c, t, e]
    return .visit { expr := newCond, proof? := some proof }
  else
    return .continue

partial def structuresPass : Pass where
  name := `structures
  run' goal := do
    let interesting := (← PreProcessM.getTypeAnalysis).interestingStructures
    if interesting.isEmpty then return goal
    let goals ← goal.casesRec fun decl => do
      if decl.isLet || decl.isImplementationDetail then
        return false
      else
        let some const := decl.type.getAppFn.constName? | return false
        return interesting.contains const
    match goals with
    | [goal] => postprocess goal interesting
    | _ => throwError "structures preprocessor generated more than 1 goal"
where
  postprocess (goal : MVarId) (interesting : Std.HashSet Name) : PreProcessM (Option MVarId) := do
    let env ← getEnv
    goal.withContext do
      let mut simprocs : Simprocs := {}
      let mut relevantLemmas : SimpTheoremsArray := #[]
      relevantLemmas ← relevantLemmas.addTheorem (.decl ``ne_eq) (← mkConstWithLevelParams ``ne_eq)
      for const in interesting do
        let constInfo ← getConstInfoInduct const
        let ctorName := (← getConstInfoCtor constInfo.ctors.head!).name
        let lemmaName := mkInjectiveEqTheoremNameFor ctorName
        if (← getEnv).find? lemmaName |>.isSome then
          trace[Meta.Tactic.bv] m!"Using injEq lemma: {lemmaName}"
          let statement ← mkConstWithLevelParams lemmaName
          relevantLemmas ← relevantLemmas.addTheorem (.decl lemmaName) statement
        let fields := (getStructureInfo env const).fieldNames.size
        let numParams := constInfo.numParams
        for proj in [0:fields] do
          -- We use the simprocs with pre such that we push in projections eagerly in order to
          -- potentially not have to simplify complex structure expressions that we only project one
          -- element out of.
          let path := mkDiscrKeyFor const numParams proj ``ite 5
          simprocs := simprocs.addCore path ``applyIteSimproc false (.inl applyIteSimproc)
          let path := mkDiscrKeyFor const numParams proj ``cond 4
          simprocs := simprocs.addCore path ``applyCondSimproc false (.inl applyCondSimproc)
      let cfg ← PreProcessM.getConfig
      let simpCtx ← Simp.mkContext
        (config := { failIfUnchanged := false, maxSteps := cfg.maxSteps })
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

  mkDiscrKeyFor (struct : Name) (structParams : Nat) (projIdx : Nat) (controlFlow : Name)
      (controlFlowParams : Nat) : Array DiscrTree.Key := Id.run do
    let stars := structParams + controlFlowParams - 1
    let mut path : Array DiscrTree.Key := Array.mkEmpty (3 + stars)
    path := path.push <| .proj struct projIdx 0
    path := path.push <| .const controlFlow controlFlowParams
    path := path.push <| .const struct structParams
    path := Nat.fold (init := path) stars (fun _ _ acc => acc.push .star)
    return path

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
