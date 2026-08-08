/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
import Lean.Meta.Tactic.BVDecide.Normalize.Simproc
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.EvalGround
import Lean.Meta.Sym.DSimp
import Lean.Meta.Sym.Simp.Forall
import Lean.Meta.Sym.Simp.ControlFlow

/-!
This module contains the implementation of the rewriting pass in the fixpoint pipeline, applying
rules from the `bv_normalize` simp set.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

/--
Responsible for applying the Bitwuzla style rewrite rules.
-/
public def rewriteRulesPass : Pass where
  name := `rewriteRules
  run' := do
    let bvThms ← bvNormalizeExt.getTheorems
    let cfg ← PreProcessM.getConfig
    let simpConfig := {
      maxSteps := cfg.maxSteps
    }
    let discharger := Sym.Simp.mkDischargerFromSimproc Sym.Simp.evalGround
    let cache ← ST.mkRef {}
    let simpMethods := {
      pre e := do
        let res ← Sym.Simp.simpControl e
        -- We invalidate `done` as we still want to rewrite in the arms, even if the discr cannot
        -- be resolved.
        match res with
        | .rfl _ cd => return .rfl false cd
        | .step e' proof _ cd => return .step e' proof false cd
      post := Sym.Simp.evalGround >> Normalize.rewriteSimproc cache >> bvThms.rewrite (d := discharger)
    }
    let dsimpConfig := { simpConfig with instances := true }
    let dsimpMethods := {
      pre := Sym.DSimp.evalGround
        >> Sym.DSimp.zeta
        >> Sym.DSimp.zetaDeltaAll
        >> Sym.DSimp.beta
        >> rewriteDsimproc
    }

    let goal ← PreProcessM.getTargetMVarId
    let changed ← goal.withContext do
      PreProcessM.mapHyps fun hyp => do
        let hyp ← dsimp dsimpMethods dsimpConfig hyp
        let hyp ← simp simpMethods simpConfig hyp
        return hyp
    if (← isTracingEnabledFor `Meta.Tactic.bv) then
      let statistics := (← cache.get).statistics.toArray.qsort (fun a b => a.2 > b.2)
      withTraceNode `Meta.Tactic.bv (fun _ => return "rewriteRules simproc statistics:") do
        for (rule, hits) in statistics do
          trace[Meta.Tactic.bv] m!"{rule}: {hits}"
    return changed
where
  dsimp (methods : Sym.DSimp.Methods) (config : Sym.DSimp.Config) (hyp : Hyp) : PreProcessM Hyp := do
    let dsimpState := { cache := ← PreProcessM.takeRewriteDSimpCache }
    let (res, s) ← Sym.DSimp.DSimpM.run (methods := methods) (config := config) (s := dsimpState) do
      Sym.DSimp.dsimp hyp.type
    PreProcessM.setRewriteDSimpCache s.cache
    hyp.applyDSimpResult res

  simp (methods : Sym.Simp.Methods) (config : Sym.Simp.Config) (hyp : Hyp) : PreProcessM Hyp := do
    let simpState := { persistentCache := ← PreProcessM.takeRewriteSimpCache }
    let (res, s) ← Sym.Simp.SimpM.run (methods := methods) (config := config) (s := simpState) do
      Sym.Simp.simp hyp.type
    PreProcessM.setRewriteSimpCache s.persistentCache
    hyp.applySimpResult res


end Normalize
end Lean.Meta.Tactic.BVDecide
