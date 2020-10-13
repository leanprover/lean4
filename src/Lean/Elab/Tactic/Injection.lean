/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Injection
import Lean.Elab.Tactic.ElabTerm
new_frontend
namespace Lean.Elab.Tactic

-- optional (" with " >> many1 ident')
private def getInjectionNewIds (stx : Syntax) : List Name :=
if stx.isNone then []
else stx[1].getArgs.toList.map Syntax.getId

private def checkUnusedIds (mvarId : MVarId) (unusedIds : List Name) : MetaM Unit := do
unless unusedIds.isEmpty do
  Meta.throwTacticEx `injection mvarId msg!"too many identifiers provided, unused: {unusedIds}"

@[builtinTactic «injection»] def evalInjection : Tactic :=
fun stx => do
  -- parser! nonReservedSymbol "injection " >> termParser >> withIds
  let fvarId ← elabAsFVar stx[1]
  let ids := getInjectionNewIds stx[2]
  liftMetaTactic fun mvarId => do
    match ← Meta.injection mvarId fvarId ids (!ids.isEmpty) with
    | Meta.InjectionResult.solved                      => checkUnusedIds mvarId ids; pure []
    | Meta.InjectionResult.subgoal mvarId' _ unusedIds => checkUnusedIds mvarId unusedIds; pure [mvarId']

end Lean.Elab.Tactic
