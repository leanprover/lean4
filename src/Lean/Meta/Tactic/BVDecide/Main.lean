/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude

public import Lean.Meta.Tactic.BVDecide.Prover.Bitblast
public import Lean.Meta.Tactic.BVDecide.Normalize
import Lean.Meta.Sym.Util


/-!
This module provides the implementation of the `bv_decide` frontend itself.
-/
namespace Lean.Meta.Tactic.BVDecide

public def TacticContext.preProcessContext (ctx : TacticContext) : Normalize.PreProcessContext where
  config := ctx.config
  restrictedTypes := ctx.restrictedTypes

def bvUnsat (g : MVarId) (hypotheses : Array Normalize.Hyp) (ctx : TacticContext) :
    Sym.SymM (Except CounterExample LratCert) :=
  M.run (hypotheses := hypotheses) do
    closeWithBVReflection g (lratBitblaster ctx)

/--
The result of calling `bv_decide`.
-/
public structure Result where
  /--
  If the normalization step was not enough to solve the goal this contains the LRAT proof
  certificate.
  -/
  lratCert : Option LratCert

/--
Try to close `g` using a bitblaster. Return either a `CounterExample` if one is found or a `Result`
if `g` is proven.
-/
public def bvDecide' (target : Normalize.Target) (ctx : TacticContext) :
    Grind.GrindM (Except CounterExample Result) := do
  Normalize.PreProcessM.run' ctx.preProcessContext target do
    let solved ← Normalize.bvNormalize
    if solved then return .ok ⟨none⟩

    match ← bvUnsat (← Normalize.PreProcessM.getTargetMVarId) (← Normalize.PreProcessM.getHyps) ctx with
    | .ok lratCert => return .ok ⟨some lratCert⟩
    | .error counterExample => return .error counterExample

/--
Call `bvDecide'` and throw a pretty error if a counter example ends up being produced.
-/
public def bvDecide (target : Normalize.Target) (ctx : TacticContext) : Grind.GrindM Result := do
  match ← bvDecide' target ctx with
  | .ok result => return result
  | .error counterExample =>
    counterExample.goal.withContext do
      let error ← explainCounterExampleQuality counterExample
      throwError (← addMessageContextFull error)


end Lean.Meta.Tactic.BVDecide
