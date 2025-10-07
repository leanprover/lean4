/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Init.Grind.Interactive
import Lean.Meta.Tactic.Grind.PP
namespace Lean.Elab.Tactic.Grind
open Meta

inductive Filter where
  | none
  | ids (declNames : NameSet) (fvarIds : FVarIdSet)

def elabFilter (filter : TSyntax ``Parser.Tactic.Grind.showFilter) : GrindTacticM Filter := do
  match filter with
  | `(Parser.Tactic.Grind.showFilter| $ids:ident,*) =>
    let mut declNames : NameSet := {}
    let mut fvarIds : FVarIdSet := {}
    for id in ids.getElems do
      match (← Term.resolveId? id) with
      | some (.const declName _) => declNames := declNames.insert declName
      | some (.fvar fvarId) => fvarIds := fvarIds.insert fvarId
      | _ => throwErrorAt id "invalid identifier"
    if declNames.isEmpty && fvarIds.isEmpty then
      return .none
    else
      return .ids declNames fvarIds
  | _ => throwUnsupportedSyntax

def Filter.match (filter : Filter) (e : Expr) : Bool :=
  match filter with
  | .none => true
  | .ids declNames fvarIds =>
    Option.isSome <| e.find? fun
      | .const declName _ => declNames.contains declName
      | .fvar fvarId => fvarIds.contains fvarId
      | _ => false

@[builtin_grind_tactic showAsserted] def evalShowAsserted : GrindTactic := fun stx => do
  match stx with
  | `(grind| show_asserted $filter:showFilter) =>
    let goal ← getMainGoal
    goal.mvarId.withContext do
      let filter ← elabFilter filter
      let facts := goal.facts.toArray.filter fun e => filter.match e
      if facts.isEmpty then
        throwError "no facts"
      logInfo <| Grind.ppExprArray `facts "Asserted facts" facts (collapsed := false)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Grind
