/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
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

@[builtinTactic Lean.Parser.Tactic.Conv.simp] def evalSimp : Tactic := fun stx => withMainContext do
  let { ctx, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
  let lhs ← getLhs
  let result ← dischargeWrapper.with fun d? => simp lhs ctx (discharge? := d?)
  applySimpResult result

@[builtinTactic Lean.Parser.Tactic.Conv.simpMatch] def evalSimpMatch : Tactic := fun stx => withMainContext do
  applySimpResult (← Split.simpMatch (← getLhs))

end Lean.Elab.Tactic.Conv
