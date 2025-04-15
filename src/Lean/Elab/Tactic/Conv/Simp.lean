/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Moritz Doll
-/
prelude
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Split
import Lean.Elab.Tactic.Conv.Basic
import Lean.Elab.Tactic.SimpTrace

namespace Lean.Elab.Tactic.Conv
open Meta Tactic TryThis

def applySimpResult (result : Simp.Result) : TacticM Unit := do
  if result.proof?.isNone then
    changeLhs result.expr
  else
    updateLhs result.expr (← result.getProof)

@[builtin_tactic Lean.Parser.Tactic.Conv.simp] def evalSimp : Tactic := fun stx => withMainContext do
  let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
  let lhs ← getLhs
  let (result, _) ← dischargeWrapper.with fun d? => simp lhs ctx (simprocs := simprocs) (discharge? := d?)
  applySimpResult result

@[builtin_tactic Lean.Parser.Tactic.Conv.simpTrace] def evalSimpTrace : Tactic := fun stx => withMainContext do
  match stx with
  | `(conv| simp?%$tk $cfg:optConfig $(discharger)? $[only%$o]? $[[$args,*]]?) => do
    let stx ← `(tactic| simp%$tk $cfg:optConfig $[$discharger]? $[only%$o]? $[[$args,*]]?)
    let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
    let lhs ← getLhs
    let (result, stats) ← dischargeWrapper.with fun d? =>
      simp lhs ctx (simprocs := simprocs) (discharge? := d?)
    applySimpResult result
    let stx ← mkSimpCallStx stx stats.usedTheorems
    addSuggestion tk stx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.Conv.simpMatch] def evalSimpMatch : Tactic := fun _ => withMainContext do
  applySimpResult (← Split.simpMatch (← getLhs))

@[builtin_tactic Lean.Parser.Tactic.Conv.dsimp] def evalDSimp : Tactic := fun stx => withMainContext do
  let { ctx, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  changeLhs (← Lean.Meta.dsimp (← getLhs) ctx).1

@[builtin_tactic Lean.Parser.Tactic.Conv.dsimpTrace] def evalDSimpTrace : Tactic := fun stx => withMainContext do
  match stx with
  | `(conv| dsimp?%$tk $cfg:optConfig $[only%$o]? $[[$args,*]]?) =>
    let stx ← `(tactic| dsimp%$tk $cfg:optConfig $[only%$o]? $[[$args,*]]?)
    let { ctx, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
    let (result, stats) ← Lean.Meta.dsimp (← getLhs) ctx
    changeLhs result
    let stx ← mkSimpCallStx stx stats.usedTheorems
    addSuggestion tk stx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Conv
