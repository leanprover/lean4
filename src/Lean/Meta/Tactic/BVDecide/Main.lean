/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude

public import Lean.Meta.Tactic.BVDecide.Prover.Bitblast
import Lean.Meta.Tactic.BVDecide.Normalize


/-!
This module provides the implementation of the `bv_decide` frontend itself.
-/
namespace Lean.Meta.Tactic.BVDecide

def bvUnsat (g : MVarId) (ctx : TacticContext) : MetaM (Except CounterExample LratCert) :=
  Sym.SymM.run <| M.run do
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
public def bvDecide' (g : MVarId) (ctx : TacticContext) : MetaM (Except CounterExample Result) := do
  Normalize.PreProcessM.run' ctx.config g do
    let solved ← Normalize.bvNormalize
    if solved then return .ok ⟨none⟩

    -- TODO: test run
    let hyps := (← Normalize.PreProcessM.getHyps).map fun hyp => {
      userName := hyp.name
      type := hyp.type
      value := hyp.value
    }
    let (_, goal) ← MVarId.assertHypotheses (← Normalize.PreProcessM.getGoal) hyps
    trace[Meta.Tactic.bv] m!"Goal handed to bvUnsat:\n{goal}"

    match ← bvUnsat goal ctx with
    | .ok lratCert => return .ok ⟨some lratCert⟩
    | .error counterExample => return .error counterExample

/--
Call `bvDecide'` and throw a pretty error if a counter example ends up being produced.
-/
public def bvDecide (g : MVarId) (ctx : TacticContext) : MetaM Result := do
  match ← bvDecide' g ctx with
  | .ok result => return result
  | .error counterExample =>
    counterExample.goal.withContext do
      let error ← explainCounterExampleQuality counterExample
      throwError (← addMessageContextFull error)


end Lean.Meta.Tactic.BVDecide
