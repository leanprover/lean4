/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Meta.InferType
import Lean.Meta.MatchUtil

namespace Lean.Meta

register_builtin_option pp.auxDecls : Bool := {
  defValue := false
  group    := "pp"
  descr    := "display auxiliary declarations used to compile recursive functions"
}

register_builtin_option pp.inaccessibleNames : Bool := {
  defValue := false
  group    := "pp"
  descr    := "display inaccessible declarations in the local context"
}

def withPPInaccessibleNamesImp (flag : Bool) (x : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun ctx => { ctx with options := pp.inaccessibleNames.setIfNotSet ctx.options flag }) x

def withPPInaccessibleNames [MonadControlT MetaM m] [Monad m] (x : m α) (flag := true) : m α :=
  mapMetaM (withPPInaccessibleNamesImp flag) x

namespace ToHide

structure State where
  hiddenInaccessibleProp : FVarIdSet := {} -- FVarIds of Propostions with inaccessible names but containing only visible names. We show only their types
  hiddenInaccessible     : FVarIdSet := {} -- FVarIds with inaccessible names, but not in hiddenInaccessibleProp
  modified               : Bool := false

structure Context where
  goalTarget : Expr

abbrev M := ReaderT Context $ StateRefT State MetaM

/- Return true if `fvarId` is marked as an hidden inaccessible or inaccessible proposition -/
def isMarked (fvarId : FVarId) : M Bool := do
  let s ← get
  return s.hiddenInaccessible.contains fvarId || s.hiddenInaccessibleProp.contains fvarId

/- If `fvarId` isMarked, then unmark it. -/
def unmark (fvarId : FVarId) : M Unit := do
  modify fun s => {
    hiddenInaccessible     := s.hiddenInaccessible.erase fvarId
    hiddenInaccessibleProp := s.hiddenInaccessibleProp.erase fvarId
    modified               := true
  }

def moveToHiddeProp (fvarId : FVarId) : M Unit := do
  modify fun s => {
    hiddenInaccessible     := s.hiddenInaccessible.erase fvarId
    hiddenInaccessibleProp := s.hiddenInaccessibleProp.insert fvarId
    modified               := true
  }

/- Return true if the given local declaration has a "visible dependency", that is, it contains
   a free variable that is `hiddenInaccessible`

   Recall that hiddenInaccessibleProps are visible, only their names are hidden -/
def hasVisibleDep (localDecl : LocalDecl) : M Bool := do
  let s ← get
  return (← getMCtx).findLocalDeclDependsOn localDecl fun fvarId =>
    !s.hiddenInaccessible.contains fvarId

/- Return true if the given local declaration has a "nonvisible dependency", that is, it contains
   a free variable that is `hiddenInaccessible` or `hiddenInaccessibleProp` -/
def hasInaccessibleNameDep (localDecl : LocalDecl) : M Bool := do
  let s ← get
  return (← getMCtx).findLocalDeclDependsOn localDecl fun fvarId =>
    s.hiddenInaccessible.contains fvarId || s.hiddenInaccessibleProp.contains fvarId

/- If `e` is visible, then any inaccessible in `e` marked as hidden should be unmarked. -/
partial def visitVisibleExpr (e : Expr) : M Unit := do
  visit (← instantiateMVars e) |>.run
where
  visit (e : Expr) : MonadCacheT Expr Unit M Unit := do
    if e.hasFVar then
      checkCache e fun _ => do
        match e with
        | Expr.forallE _ d b _   => visit d; visit b
        | Expr.lam _ d b _       => visit d; visit b
        | Expr.letE _ t v b _    => visit t; visit v; visit b
        | Expr.app f a _         => visit f; visit a
        | Expr.mdata _ b _       => visit b
        | Expr.proj _ _ b _      => visit b
        | Expr.fvar fvarId _     => if (← isMarked fvarId) then unmark fvarId
        | _                      => pure ()

def fixpointStep : M Unit := do
  visitVisibleExpr (← read).goalTarget -- The goal target is a visible forward dependency
  (← getLCtx).forM fun localDecl => do
    let fvarId := localDecl.fvarId
    if (← get).hiddenInaccessible.contains fvarId then
      if (← hasVisibleDep localDecl) then
        /- localDecl is marked to be hidden, but it has a (backward) visible dependency. -/
        unmark fvarId
      if (← isProp localDecl.type) then
        unless (← hasInaccessibleNameDep localDecl) do
          moveToHiddeProp fvarId
    else
      visitVisibleExpr localDecl.type
      match localDecl.value? with
      | some value => visitVisibleExpr value
      | _ => pure ()

partial def fixpoint : M Unit := do
  modify fun s => { s with modified := false }
  fixpointStep
  if (← get).modified then
    fixpoint

/-
If pp.inaccessibleNames == false, then collect two sets of `FVarId`s : `hiddenInaccessible` and `hiddenInaccessibleProp`
1- `hiddenInaccessible` contains `FVarId`s of free variables with inaccessible names that
    a) are not propositions or are propositions containing "visible" names.
2- `hiddenInaccessibleProp` contains `FVarId`s of free variables with inaccessible names that are propositions
   containing "visible" names.
Both sets do not contain `FVarId`s that contain visible backward or forward dependencies.
The `goalTarget` counts as a forward dependency.

We say a name is visible if it is a free variable with FVarId not in `hiddenInaccessible` nor `hiddenInaccessibleProp`
-/
def collect (goalTarget : Expr) : MetaM (FVarIdSet × FVarIdSet) := do
  if pp.inaccessibleNames.get (← getOptions) then
    /- Don't hide inaccessible names when `pp.inaccessibleNames` is set to true. -/
    return ({}, {})
  else
    let lctx ← getLCtx
    let hiddenInaccessible := lctx.foldl (init := {}) fun hiddenInaccessible localDecl => do
      if localDecl.userName.isInaccessibleUserName then
        hiddenInaccessible.insert localDecl.fvarId
      else
        hiddenInaccessible
    let (_, s) ← fixpoint.run { goalTarget := goalTarget } |>.run { hiddenInaccessible := hiddenInaccessible }
    return (s.hiddenInaccessible, s.hiddenInaccessibleProp)

end ToHide

private def addLine (fmt : Format) : Format :=
  if fmt.isNil then fmt else fmt ++ Format.line

def ppGoal (mvarId : MVarId) : MetaM Format := do
  match (← getMCtx).findDecl? mvarId with
  | none          => pure "unknown goal"
  | some mvarDecl => do
    let indent         := 2 -- Use option
    let ppAuxDecls     := pp.auxDecls.get (← getOptions)
    let lctx           := mvarDecl.lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
    withLCtx lctx mvarDecl.localInstances do
      let (hidden, hiddenProp) ← ToHide.collect mvarDecl.type
      -- The followint two `let rec`s are being used to control the generated code size.
      -- Then should be remove after we rewrite the compiler in Lean
      let rec pushPending (ids : List Name) (type? : Option Expr) (fmt : Format) : MetaM Format :=
        if ids.isEmpty then
          pure fmt
        else
          let fmt := addLine fmt
          match type? with
          | none      => pure fmt
          | some type => do
            let typeFmt ← ppExpr type
            pure $ fmt ++ (Format.joinSep ids.reverse (format " ") ++ " :" ++ Format.nest indent (Format.line ++ typeFmt)).group
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (fmt : Format) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × Format) := do
        if hiddenProp.contains localDecl.fvarId then
          let fmt ← pushPending varNames prevType? fmt
          let fmt  := addLine fmt
          let type ← instantiateMVars localDecl.type
          let typeFmt ← ppExpr type
          let fmt  := fmt ++ " : " ++ typeFmt
          pure ([], none, fmt)
        else
          match localDecl with
          | LocalDecl.cdecl _ _ varName type _   =>
            let varName := varName.simpMacroScopes
            let type ← instantiateMVars type
            if prevType? == none || prevType? == some type then
              pure (varName :: varNames, some type, fmt)
            else do
              let fmt ← pushPending varNames prevType? fmt
              pure ([varName], some type, fmt)
          | LocalDecl.ldecl _ _ varName type val _ => do
            let varName := varName.simpMacroScopes
            let fmt ← pushPending varNames prevType? fmt
            let fmt  := addLine fmt
            let type ← instantiateMVars type
            let val  ← instantiateMVars val
            let typeFmt ← ppExpr type
            let valFmt ← ppExpr val
            let fmt  := fmt ++ (format varName ++ " : " ++ typeFmt ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)).group
            pure ([], none, fmt)
      let (varNames, type?, fmt) ← lctx.foldlM (init := ([], none, Format.nil)) fun (varNames, prevType?, fmt) (localDecl : LocalDecl) =>
         if !ppAuxDecls && localDecl.isAuxDecl || hidden.contains localDecl.fvarId then
           pure (varNames, prevType?, fmt)
         else
           ppVars varNames prevType? fmt localDecl
      let fmt ← pushPending varNames type? fmt
      let fmt := addLine fmt
      let typeFmt ← ppExpr (← instantiateMVars mvarDecl.type)
      let fmt := fmt ++ "⊢ " ++ Format.nest indent typeFmt
      match mvarDecl.userName with
      | Name.anonymous => pure fmt
      | name           => return "case " ++ format name.eraseMacroScopes ++ Format.line ++ fmt

end Lean.Meta
