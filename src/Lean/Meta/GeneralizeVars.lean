/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Util.CollectFVars

namespace Lean.Meta

/--
  Add to `forbidden` all a set of `FVarId`s containing `targets` and all variables they depend on.
-/
partial def mkGeneralizationForbiddenSet (targets : Array Expr) (forbidden : FVarIdSet := {}) : MetaM FVarIdSet := do
  let mut s := { fvarSet := forbidden }
  let mut todo := #[]
  for target in targets do
    if target.isFVar then
      todo := todo.push target.fvarId!
    else
      s := collectFVars s (← instantiateMVars (← inferType target))
  loop todo.toList s.fvarSet
where
  visit (fvarId : FVarId) (todo : List FVarId) (s : FVarIdSet) : MetaM (List FVarId × FVarIdSet) := do
    let localDecl ← fvarId.getDecl
    let mut s' := collectFVars {} (← instantiateMVars localDecl.type)
    if let some val := localDecl.value? then
      s' := collectFVars s' (← instantiateMVars val)
    let mut todo := todo
    let mut s := s
    for fvarId in s'.fvarSet do
      unless s.contains fvarId do
        todo := fvarId :: todo
        s := s.insert fvarId
    return (todo, s)

  loop (todo : List FVarId) (s : FVarIdSet) : MetaM FVarIdSet := do
    match todo with
    | [] => return s
    | fvarId::todo =>
      if s.contains fvarId then
        loop todo s
      else
        let (todo, s) ← visit fvarId todo <| s.insert fvarId
        loop todo s

/--
  Collect variables to be generalized.
  It uses the following heuristic
  - Collect forward dependencies that are not in the forbidden set, and depend on some variable in `targets`.

  - We use `mkForbiddenSet` to compute `forbidden`.

  Remark: we *not* collect instance implicit arguments nor auxiliary declarations for compiling
  recursive declarations.
-/
def getFVarSetToGeneralize (targets : Array Expr) (forbidden : FVarIdSet) (ignoreLetDecls := false) : MetaM FVarIdSet := do
  let mut s : FVarIdSet := targets.foldl (init := {}) fun s target => if target.isFVar then s.insert target.fvarId! else s
  let mut r : FVarIdSet := {}
  for localDecl in (← getLCtx) do
    unless forbidden.contains localDecl.fvarId do
      unless localDecl.isAuxDecl || localDecl.binderInfo.isInstImplicit || (ignoreLetDecls && localDecl.isLet) do
      if (← findLocalDeclDependsOn localDecl (s.contains ·)) then
        r := r.insert localDecl.fvarId
        s := s.insert localDecl.fvarId
  return r

def getFVarsToGeneralize (targets : Array Expr) (forbidden : FVarIdSet := {}) (ignoreLetDecls := false) : MetaM (Array FVarId) := do
  let forbidden ← mkGeneralizationForbiddenSet targets forbidden
  let s ← getFVarSetToGeneralize targets forbidden ignoreLetDecls
  sortFVarIds s.toArray

end Lean.Meta
