/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Lean.PrettyPrinter.Delaborator.Basic
import all Lean.Elab.ErrorUtils

public section

namespace Lean.PrettyPrinter.Delaborator
open Lean.Meta

/-!
# Utilities for pretty printing metavariables and generating dynamic docstrings
-/

private def delabMVarAuxAux {α} (m : MVarId)
    (mkMVarPlaceholder : MetaM α) (mkMVar : Name → MetaM α) (mkMVarDead : Name → MetaM α)
    (ppMVars : Bool)
    (ppMVarsAnonymous : Bool) :
    MetaM α := do
  if ppMVars then
    if let some decl ← m.findDecl? then
      match decl.userName with
      | .anonymous =>
        if ppMVarsAnonymous then
          mkMVar <| Name.num `m (decl.index + 1)
        else
          mkMVarPlaceholder
      | n =>
        if some m == (← getMCtx).findUserName? n then
          mkMVar n
        else
          mkMVarDead n
    else
      -- Undefined mvar, use internal name
      mkMVar <| m.name.replacePrefix `_uniq `_mvar
  else
    mkMVarPlaceholder

/--
Constructs a `?m` term using the name of `m` or its index. Does not add terminfo.
The metavariable does not need to be type correct in the current local context.
-/
def delabMVarAux (m : MVarId) : DelabM Term := do
  delabMVarAuxAux m `(?_) (fun n => `(?$(mkIdent n)))
    (fun n =>
      let n' := addMacroScope (`_delabMVar ++ m.name) n reservedMacroScope
      `(?$(mkIdent n')))
    (ppMVars := ← getPPOption getPPMVars)
    (ppMVarsAnonymous := ← getPPOption getPPMVarsAnonymous)

/-- String version of `delabMVarAux`, for use in dynamic docstrings. -/
private def delabMVarAsStr (m : MVarId) : MetaM String := do
  delabMVarAuxAux m (pure "?_") (fun n : Name => pure <| "?" ++ n.toString)
    (fun n => pure <| "?" ++ n.toString ++ " (unreachable)")
    (ppMVars := getPPMVars (← getOptions))
    (ppMVarsAnonymous := getPPMVarsAnonymous (← getOptions))

/--
Approximate check that the application `?m a₁ … aₙ` of the delayed assignment metavariable `?m`
can be pretty printed using the pending metavariable.

Heuristic: we assume the ldecl arguments are correct, and for the cdecls we check that they are
distinct fvars
-/
def checkDelayedMVarAssignment (e : Expr) (decl : DelayedMetavarAssignment) : MetaM Bool := do
  unless e.getAppNumArgs == decl.fvars.size do
    return false
  let some mdecl ← decl.mvarIdPending.findDecl? | return false
  let mut seenFVars : FVarIdHashSet := {}
  for fvar in decl.fvars, arg in e.getAppArgs do
    let fvarId := fvar.fvarId!
    let some ldecl := mdecl.lctx.find? fvarId | return false
    unless ldecl.hasValue do
      let .fvar argFVarId := arg | return false
      if seenFVars.contains argFVarId then
        return false
      seenFVars := seenFVars.insert argFVarId
  return true

/--
Follows a chain of delayed assignments to find the pending metavariable.
-/
partial def getDelayedMVarIdPending (mvarIdPending : MVarId) : MetaM MVarId := do
  let some e ← getExprMVarAssignment? mvarIdPending | return mvarIdPending
  unless e.getAppFn'.isMVar do return mvarIdPending
  let e := (← instantiateMVars e).consumeMData
  if let .mvar mvarId := e then
    return mvarId
  let .mvar mvarId := e.getAppFn' | return mvarIdPending
  if let some decl ← getDelayedMVarAssignment? mvarId then
    unless ← checkDelayedMVarAssignment e decl do return mvarIdPending
    getDelayedMVarIdPending decl.mvarIdPending
  else
    return mvarIdPending

private def describeMVar (mvarId : MVarId) (lctxInitIndices : Nat) (fromDelayed : Bool := false) : MetaM String := do
  let delayedExpl :=
    "Substitution is delayed until the metavariable's value contains no metavariables, \
     since all occurrences of the variables from its local context will need to be \
     replaced with expressions that are valid in the current context."
  let some decl ← mvarId.findDecl? | return "[Error: This metavariable is not present in the metavariable context. Please report this issue.]"
  let mut msg := ""
  if let some { mvarIdPending, .. } ← getDelayedMVarAssignment? mvarId then
    let mvarIdPending' ← getDelayedMVarIdPending mvarIdPending
    if let some declPending' ← mvarIdPending'.findDecl? then
      msg := s!"Part of the encoding of the *delayed assignment* mechanism. \
        Represents the metavariable {← wrap <$> delabMVarAsStr mvarIdPending'}, \
        which has additional local context variables. \
        {delayedExpl}"
      if let some e ← getExprMVarAssignment? mvarIdPending' then
        msg := msg ++ (← collectAwaiting e)
      msg := msg ++ (← extraLCtxVars declPending')
    else
      msg := "[Error: This delayed assignment refers to a metavariable not present in the metavariable context. Please report this issue.]"
    return msg
  else
    match decl.kind with
    | .natural =>
      msg := "A metavariable representing an expression that should be solved for \
        by unification during the elaboration process. \
        They are created during elaboration as placeholders for implicit arguments \
        and by `_` placeholder syntax."
    | .synthetic =>
      msg := "A metavariable representing a typeclass instance whose synthesis is still pending. \
        They can be solved for by unification during the elaboration process, \
        but the inferred expression and the synthesized instance must be definitionally equal."
    | .syntheticOpaque =>
      msg := "A metavariable representing a tactic goal or an expression whose elaboration is still pending. \
        They usually act like constants until they are completely solved for. \
        They can be created using `?_` and `?n` synthetic placeholder syntax."
  unless decl.userName.isAnonymous || some mvarId == (← getMCtx).findUserName? decl.userName do
    msg := msg ++ "\n\nThis metavariable has a name but it is unreachable."
  if let some e ← getExprMVarAssignment? mvarId then
    if !fromDelayed then
      msg := msg ++ "\n\nThis metavariable has been assigned."
    else
      msg := msg ++ "\n\nThis metavariable has been assigned, but it appears here via a *delayed assignment*. " ++ delayedExpl
      msg := msg ++ (← collectAwaiting e)
  else if !(← mvarId.isAssignable) then
    msg := msg ++ "\n\nThis metavariable cannot be assigned due to the current metavariable context depth."
  else if fromDelayed then
    msg := msg ++ "\n\nThis metavariable appears here via a *delayed assignment*. " ++ delayedExpl
  if fromDelayed && !decl.lctx.isSubPrefixOf (← getLCtx) then
    msg := msg ++ (← extraLCtxVars decl)
  else
    msg := msg ++ (← absentLCtxVars decl)
  return msg
where
  wrap (n : String) := s!"`{n}`"
  namesToString (ns : List Name) : String :=
    String.intercalate ", " <| ns.map fun n => wrap <|
      if n.hasMacroScopes then
        n.eraseMacroScopes.toString ++ " (unreachable)"
      else
        n.toString
  extraLCtxVars (mdecl : MetavarDecl) : MetaM String := do
    let lctx ← getLCtx
    let ns := mdecl.lctx.foldr (init := []) fun decl ns =>
      if lctx.contains decl.fvarId then ns else decl.userName :: ns
    if ns.isEmpty then
      return ""
    else
      return s!"\n\nAdditional {ns.length.plural "variable"} in this metavariable's local context: " ++ namesToString ns
  absentLCtxVars (mdecl : MetavarDecl) : MetaM String := do
    let lctx ← getLCtx
    let lctxInitIndices := lctxInitIndices
    let ns := lctx.foldr (init := []) fun decl ns =>
      if decl.index ≥ lctxInitIndices || mdecl.lctx.contains decl.fvarId then ns else decl.userName :: ns
    if ns.isEmpty then
      return ""
    else
      return s!"\n\n{ns.length.plural "Variable"} absent from this metavariable's local context: " ++ namesToString ns
  collectAwaiting (e : Expr) : MetaM String := do
    -- Collect metavariables to diagnose why it is pending.
    let mut awaitingMVars ← getMVarsNoDelayed e
    -- Prefer reporting just the metavariables that refer to free variables not in the current context.
    let lctx ← getLCtx
    let awaitingMVars' ← awaitingMVars.filterM fun mvar => do
      let mdecl ← mvar.getDecl
      return !mdecl.lctx.isSubPrefixOf lctx
    unless awaitingMVars'.isEmpty do
      awaitingMVars := awaitingMVars'
    if awaitingMVars.isEmpty then
      return ""
    else
      let awaitingStrs ← awaitingMVars.mapM (wrap <$> delabMVarAsStr ·)
      return s!" Substitution is awaiting assignment of the following {awaitingStrs.size.plural "metavariable"}: "
        ++ String.intercalate ", " awaitingStrs.toList

/--
Creates an action that creates a description of the metavariable and its status in Markdown format,
for use in the docstring in `DelabTermInfo`.
-/
def mkDescribeMVar (mvarId : MVarId) (fromDelayed : Bool := false) :
    DelabM (PPContext → IO String) := do
  let lctxInitIndices := (← read).lctxInitIndices
  return fun ppCtx => ppCtx.runMetaM do describeMVar mvarId lctxInitIndices (fromDelayed := fromDelayed)

end Lean.PrettyPrinter.Delaborator
