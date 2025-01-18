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

def elabGrindParams (params : Grind.Params) (ps :  TSyntaxArray ``Parser.Tactic.grindParam) : MetaM Grind.Params := do
  let mut params := params
  for p in ps do
    match p with
    | `(Parser.Tactic.grindParam| - $id:ident) =>
      let declName ← realizeGlobalConstNoOverloadWithInfo id
      if (← isInductivePredicate declName) then
        throwErrorAt p "NIY"
      else
        params := { params with ematch := (← params.ematch.eraseDecl declName) }
    | `(Parser.Tactic.grindParam| $[$mod?:grindThmMod]? $id:ident) =>
      let declName ← realizeGlobalConstNoOverloadWithInfo id
      let kind ← if let some mod := mod? then Grind.getTheoremKindCore mod else pure .default
      if (← isInductivePredicate declName) then
        throwErrorAt p "NIY"
      else
        let info ← getConstInfo declName
        match info with
        | .thmInfo _ =>
          if kind == .eqBoth then
            params := { params with extra := params.extra.push (← Grind.mkEMatchTheoremForDecl declName .eqLhs) }
            params := { params with extra := params.extra.push (← Grind.mkEMatchTheoremForDecl declName .eqRhs) }
          else
            params := { params with extra := params.extra.push (← Grind.mkEMatchTheoremForDecl declName kind) }
        | .defnInfo _ =>
          if (← isReducible declName) then
            throwErrorAt p "`{declName}` is a reducible definition, `grind` automatically unfolds them"
          if kind != .eqLhs && kind != .default then
            throwErrorAt p "invalid `grind` parameter, `{declName}` is a definition, the only acceptable (and redundant) modifier is '='"
          let some thms ← Grind.mkEMatchEqTheoremsForDef? declName
            | throwErrorAt p "failed to genereate equation theorems for `{declName}`"
          params := { params with extra := params.extra ++ thms.toPArray' }
        | _ =>
          throwErrorAt p "invalid `grind` parameter, `{declName}` is not a theorem, definition, or inductive type"
    | _ => throwError "unexpected `grind` parameter{indentD p}"
  return params

def mkGrindParams (config : Grind.Config) (only : Bool) (ps :  TSyntaxArray ``Parser.Tactic.grindParam) : MetaM Grind.Params := do
  let params ← Grind.mkParams config
  let ematch ← if only then pure {} else Grind.getEMatchTheorems
  let params := { params with ematch }
  elabGrindParams params ps

def grind
    (mvarId : MVarId) (config : Grind.Config)
    (only : Bool)
    (ps   :  TSyntaxArray ``Parser.Tactic.grindParam)
    (mainDeclName : Name) (fallback : Grind.Fallback) : MetaM Unit := do
  let params ← mkGrindParams config only ps
  let goals ← Grind.main mvarId params mainDeclName fallback
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
  | `(tactic| grind $config:optConfig $[only%$only]?  $[ [$params:grindParam,*] ]? $[on_failure $fallback?]?) =>
    let fallback ← elabFallback fallback?
    let only := only.isSome
    let params := if let some params := params then params.getElems else #[]
    logWarningAt stx "The `grind` tactic is experimental and still under development. Avoid using it in production projects"
    let declName := (← Term.getDeclName?).getD `_grind
    let config ← elabGrindConfig config
    withMainContext do liftMetaFinishingTactic (grind · config only params declName fallback)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
