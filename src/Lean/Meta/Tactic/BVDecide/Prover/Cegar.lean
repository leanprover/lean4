/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.BitVec
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Function
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Lemmas

/-!
TODO
-/

namespace Lean.Meta.Tactic.BVDecide

open Cegar in
public def cegarBlaster (ctx : TacticContext) : UnsatProver LratCert := CegarM.run ctx do
  let mut lastCex := #[]
  modify fun s => { s with didChange := true }
  while ← CegarM.getDidChange do
    if (← processNewHyps) matches .solved then return .ok "" -- TODO
    CegarM.setDidChange false
    match ← checkBitVec with
    | .ok cert =>
      -- TODO: have to return learned lemmas
      return .ok cert
    | .error cex =>
      lastCex := cex
      let cex ← CegarM.CounterExample.ofArray cex
      if ← checkUf cex then continue

  return .error {
    goal := (← read).goal,
    unusedHypotheses := (← read).unusedHypotheses,
    equations := lastCex
  }

end Lean.Meta.Tactic.BVDecide
