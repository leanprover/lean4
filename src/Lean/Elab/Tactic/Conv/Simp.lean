/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Moritz Doll
-/
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Split
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

def applySimpResult (result : Simp.Result) : TacticM Unit := do
  if result.proof?.isNone then
    changeLhs result.expr
  else
    updateLhs result.expr (← result.getProof)

@[builtin_tactic Lean.Parser.Tactic.Conv.simp] def evalSimp : Tactic := fun stx => withMainContext do
  let { ctx, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
  let lhs ← getLhs
  let (result, _) ← dischargeWrapper.with fun d? => simp lhs ctx (discharge? := d?)
  applySimpResult result

@[builtin_tactic Lean.Parser.Tactic.Conv.simpMatch] def evalSimpMatch : Tactic := fun _ => withMainContext do
  applySimpResult (← Split.simpMatch (← getLhs))

@[builtin_tactic Lean.Parser.Tactic.Conv.dsimp] def evalDSimp : Tactic := fun stx => withMainContext do
  let { ctx, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  changeLhs (← Lean.Meta.dsimp (← getLhs) ctx).1

end Lean.Elab.Tactic.Conv
