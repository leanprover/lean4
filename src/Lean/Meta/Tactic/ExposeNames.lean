/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Util

namespace Lean.Meta
/--
Creates a new goal whose local context has been "exposed" so that every local declaration has a clear, accessible name.
If no local declarations require renaming, the original goal is returned unchanged.
-/
def _root_.Lean.MVarId.exposeNames (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  mvarId.checkNotAssigned `expose_names
  let mut map : Std.HashMap Name FVarId := {}
  let mut toRename := #[]
  for localDecl in (← getLCtx) do
    let userName := localDecl.userName
    if userName.hasMacroScopes then
      toRename := toRename.push localDecl.fvarId
    else
      if let some fvarId := map[userName]? then
        -- Variable has been shadowed
        toRename := toRename.push fvarId
      map := map.insert userName localDecl.fvarId
  if toRename.isEmpty then
    return mvarId
  let mut next : Std.HashMap Name Nat := {}
  let mut lctx ← getLCtx
  -- Remark: Shadowed variables may be inserted later.
  toRename := toRename.qsort fun fvarId₁ fvarId₂ =>
    (lctx.get! fvarId₁).index < (lctx.get! fvarId₂).index
  for fvarId in toRename do
    let localDecl := lctx.get! fvarId
    let mut baseName := localDecl.userName
    if baseName.hasMacroScopes then
      baseName := baseName.eraseMacroScopes
      if baseName == `x || baseName == `a then
        if (← isProp localDecl.type) then
          baseName := `h
    let mut userName := baseName
    let mut i := next[baseName]?.getD 0
    repeat
      if !map.contains userName then
        break
      i := i + 1
      userName := baseName.appendIndexAfter i
    next := next.insert baseName i
    map := map.insert userName fvarId
    lctx := lctx.modifyLocalDecl fvarId (·.setUserName userName)
  let mvarNew ← mkFreshExprMVarAt lctx (← getLocalInstances) (← mvarId.getType) .syntheticOpaque (← mvarId.getTag)
  mvarId.assign mvarNew
  return mvarNew.mvarId!

end Lean.Meta
