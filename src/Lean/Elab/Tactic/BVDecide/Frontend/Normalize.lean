/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.FalseOrByContra
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.ApplyControlFlow
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Simproc
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Rewrite
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.AndFlatten
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.EmbeddedConstraint
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.AC
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Structures
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.IntToBitVec
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Enums
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis

/-!
This module contains the implementation of `bv_normalize`, the preprocessing tactic for `bv_decide`.
It is in essence a (slightly reduced) version of the Bitwuzla preprocessor together with Lean
specific details.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

def passPipeline : PreProcessM (List Pass) := do
  let mut passPipeline := [rewriteRulesPass]
  let cfg ← PreProcessM.getConfig

  if cfg.acNf then
    passPipeline := passPipeline ++ [acNormalizePass]

  if cfg.andFlattening then
    passPipeline := passPipeline ++ [andFlatteningPass]

  if cfg.embeddedConstraintSubst then
    passPipeline := passPipeline ++ [embeddedConstraintPass]

  return passPipeline

def bvNormalize (g : MVarId) (cfg : BVDecideConfig) : MetaM (Option MVarId) := do
  withTraceNode `Meta.Tactic.bv (fun _ => return "Preprocessing goal") do
    (go g).run cfg g
where
  go (g : MVarId) : PreProcessM (Option MVarId) := do
    let some g' ← g.falseOrByContra | return none
    let mut g := g'

    trace[Meta.Tactic.bv] m!"Running preprocessing pipeline on:\n{g}"
    let cfg ← PreProcessM.getConfig

    if cfg.structures || cfg.enums then
      g := (← typeAnalysisPass.run g).get!

    /-
    There is a tension between the structures and enums pass at play:
    1. Enums should run before structures as it could convert matches on enums into `cond`
       chains. This in turn can be used by the structures pass to float projections into control
       flow which might be necessary.
    2. Structures should run before enums as it could reveal new facts about enums that we might
       need to handle. For example a structure might contain a field that contains a fact about
       some enum. This fact needs to be processed properly by the enums pass

    To resolve this tension we do the following:
    1. Run the structures pass (if enabled)
    2. Run the enums pass (if enabled)
    3. Within the enums pass we rerun the part of the structures pass that could profit from the
       enums pass as described above. This comes down to adding a few more lemmas to a simp
       invocation that is going to happen in the enums pass anyway and should thus be cheap.
    -/
    if cfg.structures then
      let some g' ← structuresPass.run g | return none
      g := g'

    if cfg.enums then
      let some g' ← enumsPass.run g | return none
      g := g'

    if cfg.fixedInt then
      let some g' ← intToBitVecPass.run g | return none
      g := g'

    trace[Meta.Tactic.bv] m!"Running fixpoint pipeline on:\n{g}"
    let pipeline ← passPipeline
    Pass.fixpointPipeline pipeline g

@[builtin_tactic Lean.Parser.Tactic.bvNormalize]
def evalBVNormalize : Tactic := fun
  | `(tactic| bv_normalize $cfg:optConfig) => do
    let cfg ← elabBVDecideConfig cfg
    let g ← getMainGoal
    match ← bvNormalize g cfg with
    | some newGoal => replaceMainGoal [newGoal]
    | none => replaceMainGoal []
  | _ => throwUnsupportedSyntax

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
