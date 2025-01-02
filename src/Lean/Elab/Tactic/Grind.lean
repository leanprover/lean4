/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Tactics
import Lean.Meta.Tactic.Grind
import Lean.Elab.Command
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Config

namespace Lean.Elab.Tactic
open Meta

declare_config_elab elabGrindConfig Grind.Config

open Command Term in
@[builtin_command_elab Lean.Parser.Command.grindPattern]
def elabGrindPattern : CommandElab := fun stx => do
  match stx with
  | `(grind_pattern $thmName:ident => $terms,*) => do
    liftTermElabM do
      let declName ← resolveGlobalConstNoOverload thmName
      discard <| addTermInfo thmName (← mkConstWithLevelParams declName)
      let info ← getConstInfo declName
      forallTelescope info.type fun xs _ => do
        let patterns ← terms.getElems.mapM fun term => do
          let pattern ← instantiateMVars (← elabTerm term none)
          let pattern ← Grind.unfoldReducible pattern
          return pattern.abstract xs
        Grind.addEMatchTheorem declName xs.size patterns.toList
  | _ => throwUnsupportedSyntax

def grind (mvarId : MVarId) (config : Grind.Config) (mainDeclName : Name) : MetaM Unit := do
  let mvarIds ← Grind.main mvarId config mainDeclName
  unless mvarIds.isEmpty do
    throwError "`grind` failed\n{goalsToMessageData mvarIds}"

@[builtin_tactic Lean.Parser.Tactic.grind] def evalApplyRfl : Tactic := fun stx => do
  match stx with
  | `(tactic| grind $config:optConfig) =>
    logWarningAt stx "The `grind` tactic is experimental and still under development. Avoid using it in production projects"
    let declName := (← Term.getDeclName?).getD `_grind
    let config ← elabGrindConfig config
    withMainContext do liftMetaFinishingTactic (grind · config declName)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
