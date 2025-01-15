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
          let pattern ← elabTerm term none
          synthesizeSyntheticMVarsUsingDefault
          let pattern ← instantiateMVars pattern
          let pattern ← Grind.preprocessPattern pattern
          return pattern.abstract xs
        Grind.addEMatchTheorem declName xs.size patterns.toList
  | _ => throwUnsupportedSyntax

def grind (mvarId : MVarId) (config : Grind.Config) (mainDeclName : Name) (fallback : Grind.Fallback) : MetaM Unit := do
  let goals ← Grind.main mvarId config mainDeclName fallback
  unless goals.isEmpty do
    throwError "`grind` failed\n{← Grind.goalsToMessageData goals config}"

private def elabFallback (fallback? : Option Term) : TermElabM (Grind.GoalM Unit) := do
  let some fallback := fallback? | return (pure ())
  let type := mkApp (mkConst ``Grind.GoalM) (mkConst ``Unit)
  let value ← withLCtx {} {} do Term.elabTermAndSynthesize fallback type
  let auxDeclName ← if let .const declName _ := value then
    pure declName
  else
    let auxDeclName ← Term.mkAuxName `_grind_fallback
    let decl := Declaration.defnDecl {
      name := auxDeclName
      levelParams := []
      type, value, hints := .opaque, safety := .safe
    }
    addAndCompile decl
    pure auxDeclName
  unsafe evalConst (Grind.GoalM Unit) auxDeclName

@[builtin_tactic Lean.Parser.Tactic.grind] def evalApplyRfl : Tactic := fun stx => do
  match stx with
  | `(tactic| grind $config:optConfig $[on_failure $fallback?]?) =>
    let fallback ← elabFallback fallback?
    logWarningAt stx "The `grind` tactic is experimental and still under development. Avoid using it in production projects"
    let declName := (← Term.getDeclName?).getD `_grind
    let config ← elabGrindConfig config
    withMainContext do liftMetaFinishingTactic (grind · config declName fallback)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
