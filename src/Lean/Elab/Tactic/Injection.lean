/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Injection
import Lean.Elab.Tactic.ElabTerm
namespace Lean.Elab.Tactic

-- optional (" with " >> many1 ident')
private def getInjectionNewIds (stx : Syntax) : List Name :=
  if stx.isNone then
    []
  else
    stx[1].getArgs.toList.map getNameOfIdent'

private def checkUnusedIds (tacticName : Name) (mvarId : MVarId) (unusedIds : List Name) : MetaM Unit :=
  unless unusedIds.isEmpty do
    Meta.throwTacticEx tacticName mvarId m!"too many identifiers provided, unused: {unusedIds}"

@[builtin_tactic «injection»] def evalInjection : Tactic := fun stx => do
  -- leading_parser nonReservedSymbol "injection " >> termParser >> withIds
  let fvarId ← elabAsFVar stx[1]
  let ids := getInjectionNewIds stx[2]
  liftMetaTactic fun mvarId => do
    match (← Meta.injection mvarId fvarId ids) with
    | .solved                      => checkUnusedIds `injection mvarId ids; return []
    | .subgoal mvarId' _ unusedIds => checkUnusedIds `injection mvarId unusedIds; return [mvarId']

@[builtin_tactic «injections»] def evalInjections : Tactic := fun stx => do
  let ids := stx[1].getArgs.toList.map getNameOfIdent'
  liftMetaTactic fun mvarId => do
    match (← Meta.injections mvarId ids) with
    | .solved                    => checkUnusedIds `injections mvarId ids; return []
    | .subgoal mvarId' unusedIds => checkUnusedIds `injections mvarId unusedIds; return [mvarId']

end Lean.Elab.Tactic
