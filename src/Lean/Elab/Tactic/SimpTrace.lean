/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

prelude
public import Lean.Elab.ElabRules
public import Lean.Elab.Tactic.Simp
public import Lean.Meta.Tactic.TryThis
public import Lean.LibrarySuggestions.Basic

public section

/-!
# `simp?` tactic

The `simp?` tactic is a simple wrapper around the simp with trace behavior.
-/
namespace Lean.Elab.Tactic
open Lean Elab Parser Tactic Meta Simp Tactic.TryThis

/-- Filter out `+suggestions` and `+locals` from the config syntax -/
def filterSuggestionsAndLocalsFromSimpConfig (cfg : TSyntax ``Lean.Parser.Tactic.optConfig) :
    MetaM (TSyntax ``Lean.Parser.Tactic.optConfig) := do
  -- The config has one arg: a null node containing configItem nodes
  let nullNode := cfg.raw.getArg 0
  let configItems := nullNode.getArgs

  -- Filter out configItem nodes that contain +suggestions or +locals
  let filteredItems := configItems.filter fun item =>
    match item[0]?, item.getKind with
    | some posConfigItem, ``Lean.Parser.Tactic.configItem =>
      match posConfigItem[1]?, posConfigItem.getKind with
      | some ident, ``Lean.Parser.Tactic.posConfigItem =>
        let id := ident.getId.eraseMacroScopes
        id != `suggestions && id != `locals
      | _, _ => true
    | _, _ => true

  -- Reconstruct the config with filtered items
  let newNullNode := nullNode.setArgs filteredItems
  return ⟨cfg.raw.setArg 0 newNullNode⟩

open TSyntax.Compat in
/-- Constructs the syntax for a simp call, for use with `simp?`. -/
def mkSimpCallStx (stx : Syntax) (usedSimps : UsedSimps) : MetaM (TSyntax `tactic) := do
  let stx := stx.unsetTrailing
  mkSimpOnly stx usedSimps

@[builtin_tactic simpTrace] def evalSimpTrace : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  match stx with
  | `(tactic|
      simp?%$tk $[!%$bang]? $cfg:optConfig $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) =>
    -- Check if premise selection is enabled
    let config ← elabSimpConfig cfg (kind := .simp)
    let mut argsArray : TSyntaxArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] :=
      if let some a := args then a.getElems else #[]
    if config.suggestions then
      -- Get premise suggestions from the premise selector
      let suggestions ← Lean.LibrarySuggestions.select (← getMainGoal) { caller := some "simp" }
      -- Convert suggestions to simp argument syntax and add them to the args
      -- If a name is ambiguous, we add ALL interpretations
      for sugg in suggestions do
        let ident := mkIdent sugg.name
        let candidates ← resolveGlobalConst ident
        for candidate in candidates do
          let arg ← `(Parser.Tactic.simpLemma| $(mkCIdentFrom ident candidate (canonical := true)):term)
          argsArray := argsArray.push arg
    -- Build the simp syntax with the updated arguments
    let stxForExecution ← if bang.isSome then
      `(tactic| simp!%$tk $cfg:optConfig $[$discharger]? $[only%$o]? [$argsArray,*] $[$loc]?)
    else
      `(tactic| simp%$tk $cfg:optConfig $[$discharger]? $[only%$o]? [$argsArray,*] $[$loc]?)
    -- Build syntax for suggestion (without +suggestions config)
    let filteredCfg ← filterSuggestionsAndLocalsFromSimpConfig cfg
    let stxForSuggestion ← if bang.isSome then
      `(tactic| simp!%$tk $filteredCfg:optConfig $[$discharger]? $[only%$o]? [$argsArray,*] $[$loc]?)
    else
      `(tactic| simp%$tk $filteredCfg:optConfig $[$discharger]? $[only%$o]? [$argsArray,*] $[$loc]?)
    let { ctx, simprocs, dischargeWrapper, ..} ← mkSimpContext stxForExecution (eraseLocal := false)
    let ctx := if bang.isSome then ctx.setAutoUnfold else ctx
    let stats ← dischargeWrapper.with fun discharge? =>
      simpLocation ctx (simprocs := simprocs) discharge? <|
        (loc.map expandLocation).getD (.targets #[] true)
    let stx ← mkSimpCallStx stxForSuggestion stats.usedTheorems
    addSuggestion tk stx (origSpan? := ← getRef)
    return stats.diag
  | _ => throwUnsupportedSyntax

@[builtin_tactic simpAllTrace] def evalSimpAllTrace : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  match stx with
  | `(tactic| simp_all?%$tk $[!%$bang]? $cfg:optConfig $(discharger)? $[only%$o]? $[[$args,*]]?) =>
    -- Check if premise selection is enabled
    let config ← elabSimpConfig cfg (kind := .simpAll)
    let mut argsArray : TSyntaxArray [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] :=
      if let some a := args then a.getElems else #[]
    if config.suggestions then
      -- Get premise suggestions from the premise selector
      let suggestions ← Lean.LibrarySuggestions.select (← getMainGoal) { caller := some "simp_all" }
      -- Convert suggestions to simp argument syntax and add them to the args
      -- If a name is ambiguous, we add ALL interpretations
      for sugg in suggestions do
        let ident := mkIdent sugg.name
        let candidates ← resolveGlobalConst ident
        for candidate in candidates do
          let arg ← `(Parser.Tactic.simpLemma| $(mkCIdentFrom ident candidate (canonical := true)):term)
          argsArray := argsArray.push arg
    -- Build the simp_all syntax with the updated arguments
    let stxForExecution ←
      if argsArray.isEmpty then
        if bang.isSome then
          `(tactic| simp_all!%$tk $cfg:optConfig $[$discharger]? $[only%$o]?)
        else
          `(tactic| simp_all%$tk $cfg:optConfig $[$discharger]? $[only%$o]?)
      else
        if bang.isSome then
          `(tactic| simp_all!%$tk $cfg:optConfig $[$discharger]? $[only%$o]? [$argsArray,*])
        else
          `(tactic| simp_all%$tk $cfg:optConfig $[$discharger]? $[only%$o]? [$argsArray,*])
    -- Build syntax for suggestion (without +suggestions config)
    let filteredCfg ← filterSuggestionsAndLocalsFromSimpConfig cfg
    let stxForSuggestion ←
      if argsArray.isEmpty then
        if bang.isSome then
          `(tactic| simp_all!%$tk $filteredCfg:optConfig $[$discharger]? $[only%$o]?)
        else
          `(tactic| simp_all%$tk $filteredCfg:optConfig $[$discharger]? $[only%$o]?)
      else
        if bang.isSome then
          `(tactic| simp_all!%$tk $filteredCfg:optConfig $[$discharger]? $[only%$o]? [$argsArray,*])
        else
          `(tactic| simp_all%$tk $filteredCfg:optConfig $[$discharger]? $[only%$o]? [$argsArray,*])
    let { ctx, simprocs, .. } ← mkSimpContext stxForExecution (eraseLocal := true)
      (kind := .simpAll) (ignoreStarArg := true)
    let ctx := if bang.isSome then ctx.setAutoUnfold else ctx
    let (result?, stats) ← simpAll (← getMainGoal) ctx (simprocs := simprocs)
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    let stx ← mkSimpCallStx stxForSuggestion stats.usedTheorems
    addSuggestion tk stx (origSpan? := ← getRef)
    return stats.diag
  | _ => throwUnsupportedSyntax

/-- Implementation of `dsimp?`. -/
def dsimpLocation' (ctx : Simp.Context) (simprocs : SimprocsArray) (loc : Location) :
    TacticM Simp.Stats := do
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
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Simp.Stats := do
    let mvarId ← getMainGoal
    let (result?, stats) ← dsimpGoal mvarId ctx simprocs (simplifyTarget := simplifyTarget)
      (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    pure stats

@[builtin_tactic dsimpTrace] def evalDSimpTrace : Tactic := fun stx => withMainContext do withSimpDiagnostics do
  match stx with
  | `(tactic| dsimp?%$tk $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]? $(loc)?) =>
    let stx ← if bang.isSome then
      `(tactic| dsimp!%$tk $cfg:optConfig $[only%$o]? $[[$args,*]]? $(loc)?)
    else
      `(tactic| dsimp%$tk $cfg:optConfig $[only%$o]? $[[$args,*]]? $(loc)?)
    let { ctx, simprocs, .. } ←
      withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
    let ctx := if bang.isSome then ctx.setAutoUnfold else ctx
    let stats ← dsimpLocation' ctx simprocs <| (loc.map expandLocation).getD (.targets #[] true)
    let stx ← mkSimpCallStx stx stats.usedTheorems
    addSuggestion tk stx (origSpan? := ← getRef)
    return stats.diag
  | _ => throwUnsupportedSyntax
