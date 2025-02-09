/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Revert

namespace Lean.Meta.Grind
/--
Reverts all free variables in the goal `mvarId`.
**Remark**: Auxiliary local declarations are cleared.
The `grind` tactic also clears them, but this tactic can be used independently by users.
-/
def _root_.Lean.MVarId.revertAll (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  mvarId.checkNotAssigned `revertAll
  let mut toRevert := #[]
  for fvarId in (← getLCtx).getFVarIds do
    unless (← fvarId.getDecl).isAuxDecl do
      toRevert := toRevert.push fvarId
  mvarId.setKind .natural
  let (_, mvarId) ← mvarId.revert toRevert
    (preserveOrder := true)
    (clearAuxDeclsInsteadOfRevert := true)
  return mvarId

end Lean.Meta.Grind
