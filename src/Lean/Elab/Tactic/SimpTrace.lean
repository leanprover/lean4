/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Lean.Elab.ElabRules
import Lean.Elab.Tactic.Simp
import Lean.Meta.Tactic.TryThis

/-!
# `simp?` tactic

The `simp?` tactic is a simple wrapper around the simp with trace behavior.
-/
namespace Lean.Elab.Tactic
open Lean Elab Parser Tactic Meta Simp Tactic.TryThis

open TSyntax.Compat in
/-- Constructs the syntax for a simp call, for use with `simp?`. -/
def mkSimpCallStx (stx : Syntax) (usedSimps : UsedSimps) : MetaM (TSyntax `tactic) := do
  let stx := stx.unsetTrailing
  mkSimpOnly stx usedSimps

@[builtin_tactic simpTrace] def evalSimpTrace : Tactic := fun stx =>
  match stx with
  | `(tactic|
      simp?%$tk $[!%$bang]? $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) => withMainContext do
    let stx ← if bang.isSome then
      `(tactic| simp!%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?)
    else
      `(tactic| simp%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?)
    let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false)
    let usedSimps ← dischargeWrapper.with fun discharge? =>
      simpLocation ctx (simprocs := simprocs) discharge? <|
        (loc.map expandLocation).getD (.targets #[] true)
    let stx ← mkSimpCallStx stx usedSimps
    addSuggestion tk stx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

@[builtin_tactic simpAllTrace] def evalSimpAllTrace : Tactic := fun stx =>
  match stx with
  | `(tactic| simp_all?%$tk $[!%$bang]? $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?) => do
    let stx ← if bang.isSome then
      `(tactic| simp_all!%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?)
    else
      `(tactic| simp_all%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?)
    let { ctx, .. } ← mkSimpContext stx (eraseLocal := true)
      (kind := .simpAll) (ignoreStarArg := true)
    let (result?, usedSimps) ← simpAll (← getMainGoal) ctx
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    let stx ← mkSimpCallStx stx usedSimps
    addSuggestion tk stx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

/-- Implementation of `dsimp?`. -/
def dsimpLocation' (ctx : Simp.Context) (simprocs : SimprocsArray) (loc : Location) :
    TacticM Simp.UsedSimps := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  /-- Implementation of `dsimp?`. -/
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Simp.UsedSimps := do
    let mvarId ← getMainGoal
    let (result?, usedSimps) ← dsimpGoal mvarId ctx simprocs (simplifyTarget := simplifyTarget)
      (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    pure usedSimps

@[builtin_tactic dsimpTrace] def evalDSimpTrace : Tactic := fun stx =>
  match stx with
  | `(tactic| dsimp?%$tk $[!%$bang]? $(config)? $[only%$o]? $[[$args,*]]? $(loc)?) => do
    let stx ← if bang.isSome then
      `(tactic| dsimp!%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?)
    else
      `(tactic| dsimp%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?)
    let { ctx, simprocs, .. } ←
      withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
    let usedSimps ← dsimpLocation' ctx simprocs <| (loc.map expandLocation).getD (.targets #[] true)
    let stx ← mkSimpCallStx stx usedSimps
    addSuggestion tk stx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax
