/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Tactic.Injection
import Init.Lean.Elab.Tactic.ElabTerm

namespace Lean
namespace Elab
namespace Tactic

-- optional (" with " >> many1 ident')
private def getInjectionNewIds (stx : Syntax) : List Name :=
if stx.isNone then []
else (stx.getArg 1).getArgs.toList.map Syntax.getId

@[builtinTactic «injection»] def evalInjection : Tactic :=
fun stx => do
  -- parser! nonReservedSymbol "injection " >> termParser >> withIds
  fvarId ← elabAsFVar (stx.getArg 1);
  let ids := getInjectionNewIds (stx.getArg 2);
  liftMetaTactic stx $ fun mvarId => do
    r ← Meta.injection mvarId fvarId ids (!ids.isEmpty);
    match r with
    | Meta.InjectionResult.solved             => pure []
    | Meta.InjectionResult.subgoal mvarId _ _ => pure [mvarId]

end Tactic
end Elab
end Lean
