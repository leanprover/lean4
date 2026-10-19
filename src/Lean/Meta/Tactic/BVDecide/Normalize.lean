/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
public import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow
public import Lean.Meta.Tactic.BVDecide.Normalize.Simproc
public import Lean.Meta.Tactic.BVDecide.Normalize.Rewrite
public import Lean.Meta.Tactic.BVDecide.Normalize.AndFlatten
public import Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint
public import Lean.Meta.Tactic.BVDecide.Normalize.AC
public import Lean.Meta.Tactic.BVDecide.Normalize.Structures
public import Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec
public import Lean.Meta.Tactic.BVDecide.Normalize.Enums
public import Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis
public import Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit
public import Lean.Meta.Tactic.BVDecide.Normalize.Reduction
public import Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps
public import Lean.Meta.Tactic.BVDecide.EPR.Pass
import Lean.Meta.Sym.Util
import Lean.Meta.Sym.AbstractS
import Lean.Meta.Sym.Intro
import Lean.Meta.Sym.Grind
import Lean.Meta.Tactic.Grind.BVDecide.Types

/-!
This module contains the implementation of `bv_normalize`, the preprocessing tactic for `bv_decide`.
It is in essence a (slightly reduced) version of the Bitwuzla preprocessor together with Lean
specific details.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

def passPipeline : PreProcessM (List Pass) := do
  let mut passPipeline := [rewriteRulesPass]
  let cfg ← PreProcessM.getConfig

  if cfg.acNf then
    passPipeline := passPipeline ++ [bvAcNormalizePass]

  if cfg.embeddedConstraintSubst && cfg.andFlattening then
    passPipeline := passPipeline ++ [andFlatteningPass]

  if cfg.embeddedConstraintSubst then
    passPipeline := passPipeline ++ [embeddedConstraintPass]

  return passPipeline

/--
Runs `x` with the caches that a previous `bv_decide_push` left in the grind goal. In
`bv_decide_push` mode the caches of this run are handed back to the goal afterwards, such that
future invocations of the pre-processor on this goal can pick them up again.
-/
def withCaches (x : PreProcessM α) : PreProcessM α := do
  if let some caches ← PreProcessM.withGrindGoal Grind.BVDecide.getCaches then
    PreProcessM.setCaches caches
  let res ← x
  if ← PreProcessM.isPushMode then
    discard <| PreProcessM.withGrindGoal <| Grind.BVDecide.setCaches (← PreProcessM.getCaches)
  return res

structure RewrittenProp where
  type : Expr
  type' : Expr
  proof? : Option Expr

/--
We run rewriting on the EPR quantifiers once ahead of time so we do not re-normalize them during
MBQI over and over again. However, in order to ease later processing we do not just normalize them
fully but instead keep the guards as separate implications, i.e. go from
```
∀ (x₁ ... xₙ), guard x₁ → ... → guard xₙ → body x₁ ... xₙ
```
to
```
∀ (x₁ ... xₙ), normalized_guard x₁ = true → ... → normalized_guard xₙ = true → normalized_body x₁ ... xₙ = true
```
This is done as during instantiation we can always simplify away all guard conditions trivially.
-/
public def normalizeEprQuantifiers : PreProcessM Unit := do
  let problem := (← get).eprBvProblem
  if problem.quantifiedFacts.isEmpty then return
  withTraceNode `Meta.Tactic.bv.epr (fun _ => return m!"Normalizing quantified facts") do
    let facts ← withRewriteRules fun dsimpMethods dsimpConfig simpMethods simpConfig => do
      let rewrite (type : Expr) : PreProcessM RewrittenProp := do
        let hyp ← PreProcessM.dsimpHyp .rewrite dsimpMethods dsimpConfig
          { name := .anonymous, type, value := type, source := .epr }
        match ← PreProcessM.simpExpr .rewrite simpMethods simpConfig hyp.type with
        | .rfl .. => return { type := hyp.type, type' := hyp.type, proof? := none }
        | .step type' proof .. => return { type := hyp.type, type', proof? := some proof }
      problem.quantifiedFacts.filterMapM (normalizeEprFact rewrite)
    modify fun s => { s with eprBvProblem := { problem with quantifiedFacts := facts } }
where
  normalizeEprFact (rewrite : Expr → PreProcessM RewrittenProp) (fact : EPR.QuantifiedFact) :
      PreProcessM (Option EPR.QuantifiedFact) := do
    let n := fact.boundSorts.size
    forallBoundedTelescope fact.hyp.type (some (2 * n)) fun xs body => do
      assert! xs.size == 2 * n
      let args := xs[0...n].toArray
      let guards := xs[n...*].toArray
      let body ← rewrite (← Sym.shareCommon body)
      if body.type'.isTrue then return none
      let guards ← guards.mapM fun guard => do
        rewrite (← Sym.shareCommon (← guard.fvarId!.getType))
      withLocalDeclsDND (guards.map fun guard => (.anonymous, guard.type')) fun newGuards => do
        let binders := args ++ newGuards
        let type ← Sym.mkForallFVarsS binders body.type'
        let guardProofs := newGuards.zipWith (bs := guards) fun newGuard guard =>
          match guard.proof? with
          | some proof => mkApp4 (mkConst ``Eq.mpr [0]) guard.type guard.type' proof newGuard
          | none => newGuard
        let proof := mkAppN fact.hyp.value (args ++ guardProofs)
        let proof :=
          match body.proof? with
          | some bodyProof => mkApp4 (mkConst ``Eq.mp [0]) body.type body.type' bodyProof proof
          | none => proof
        let proof ← mkLambdaFVars binders proof
        trace[Meta.Tactic.bv.epr] m!"normalized quantified fact: {type}"
        return some { fact with hyp := { fact.hyp with type, value := proof } }


public def bvNormalize (hyps? : Option (Array Hyp) := none) : PreProcessM Bool := do
  withTraceNode `Meta.Tactic.bv (fun _ => return "Preprocessing goal") do
    if let some hyps := hyps? then
      modify fun s => { s with hypotheses := hyps }
    else
      if ← PreProcessM.collectTargetHyps then return true
    withCaches runPipeline
where
  /--
  Runs all passes on the hypotheses collected from the target. Returns `true` if a pass closed the
  goal.
  -/
  runPipeline : PreProcessM Bool := do
    trace[Meta.Tactic.bv] m!"Running preprocessing pipeline"
    let cfg ← PreProcessM.getConfig

    if cfg.structures || cfg.enums then
      if ← typeAnalysisPass.run then return true

    if ← reductionPass.run then return true

    if cfg.epr then
      if ← EPR.eprDetectPass.run then return true

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
      if ← structuresPass.run then return true

    if cfg.enums then
      if ← enumsPass.run then return true

    if cfg.fixedInt then
      if ← intToBitVecPass.run then return true

    let pipeline ← passPipeline
    if ← Pass.fixpointPipeline pipeline then return true
    /-
    Run short circuiting once post fixpoint, as it increases the size of terms with
    the aim of exposing potential short-circuit reasoning to the solver.
    -/
    if cfg.shortCircuit then
      if ← shortCircuitPass.run then return true

    return false

end Normalize
end Lean.Meta.Tactic.BVDecide
