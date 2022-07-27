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

register_builtin_option pp.showLetValues : Bool := {
  defValue := false
  group    := "pp"
  descr    := "display let-declaration values in the info view"
}

def withPPInaccessibleNamesImp (flag : Bool) (x : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun ctx => { ctx with options := pp.inaccessibleNames.setIfNotSet ctx.options flag }) x

def withPPInaccessibleNames [MonadControlT MetaM m] [Monad m] (x : m α) (flag := true) : m α :=
  mapMetaM (withPPInaccessibleNamesImp flag) x

def withPPShowLetValuesImp (flag : Bool) (x : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun ctx => { ctx with options := pp.showLetValues.setIfNotSet ctx.options flag }) x

def withPPShowLetValues [MonadControlT MetaM m] [Monad m] (x : m α) (flag := true) : m α :=
  mapMetaM (withPPShowLetValuesImp flag) x

/--
Set pretty-printing options (`pp.showLetValues = true` and `pp.inaccessibleNames = true`) for visualizing goals.
-/
def withPPForTacticGoal [MonadControlT MetaM m] [Monad m] (x : m α) : m α :=
  withPPShowLetValues <| withPPInaccessibleNames x

namespace ToHide

structure State where
  /-- FVarIds of Propostions with inaccessible names but containing only visible names. We show only their types -/
  hiddenInaccessibleProp : FVarIdSet := {}
  /-- FVarIds with inaccessible names, but not in hiddenInaccessibleProp -/
  hiddenInaccessible     : FVarIdSet := {}
  modified               : Bool := false

structure Context where
  /--
   If true we make a declaration "visible" if it has visible backward dependencies.
   Remark: recall that for the `Prop` case, the declaration is moved to `hiddenInaccessibleProp`
   -/
  backwardDeps  : Bool
  goalTarget    : Expr
  showLetValues : Bool

abbrev M := ReaderT Context $ StateRefT State MetaM

/-- Return true if `fvarId` is marked as an hidden inaccessible or inaccessible proposition -/
def isMarked (fvarId : FVarId) : M Bool := do
  let s ← get
  return s.hiddenInaccessible.contains fvarId || s.hiddenInaccessibleProp.contains fvarId

/-- If `fvarId` isMarked, then unmark it. -/
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

/-- Similar to `findLocalDeclDependsOn`, but it only considers `let`-values if `showLetValues = true` -/
private def findDeps (localDecl : LocalDecl) (f : FVarId → Bool) : M Bool := do
  if (← read).showLetValues then
    findLocalDeclDependsOn localDecl f
  else
    findExprDependsOn localDecl.type f

/-- Return true if the given local declaration has a "visible dependency", that is, it contains
   a free variable that is `hiddenInaccessible`

   Recall that hiddenInaccessibleProps are visible, only their names are hidden -/
def hasVisibleDep (localDecl : LocalDecl) : M Bool := do
  let s ← get
  findDeps localDecl (!s.hiddenInaccessible.contains ·)

/-- Return true if the given local declaration has a "nonvisible dependency", that is, it contains
   a free variable that is `hiddenInaccessible` or `hiddenInaccessibleProp` -/
def hasInaccessibleNameDep (localDecl : LocalDecl) : M Bool := do
  let s ← get
  findDeps localDecl fun fvarId =>
    s.hiddenInaccessible.contains fvarId || s.hiddenInaccessibleProp.contains fvarId

/-- If `e` is visible, then any inaccessible in `e` marked as hidden should be unmarked. -/
partial def visitVisibleExpr (e : Expr) : M Unit := do
  visit (← instantiateMVars e) |>.run
where
  visit (e : Expr) : MonadCacheT Expr Unit M Unit := do
    if e.hasFVar then
      checkCache e fun _ => do
        match e with
        | .forallE _ d b _   => visit d; visit b
        | .lam _ d b _       => visit d; visit b
        | .letE _ t v b _    => visit t; visit v; visit b
        | .app f a           => visit f; visit a
        | .mdata _ b         => visit b
        | .proj _ _ b        => visit b
        | .fvar fvarId       => if (← isMarked fvarId) then unmark fvarId
        | _                  => return ()

def fixpointStep : M Unit := do
  visitVisibleExpr (← read).goalTarget -- The goal target is a visible forward dependency
  (← getLCtx).forM fun localDecl => do
    let fvarId := localDecl.fvarId
    if (← get).hiddenInaccessible.contains fvarId then
      if (← read).backwardDeps then
        if (← hasVisibleDep localDecl) then
          /- localDecl is marked to be hidden, but it has a (backward) visible dependency. -/
          unmark fvarId
        if (← isProp localDecl.type) then
          unless (← hasInaccessibleNameDep localDecl) do
            moveToHiddeProp fvarId
    else
      visitVisibleExpr localDecl.type
      if (← read).showLetValues then
        let some value := localDecl.value? | return ()
        visitVisibleExpr value

partial def fixpoint : M Unit := do
  modify fun s => { s with modified := false }
  fixpointStep
  if (← get).modified then
    fixpoint

/--
  Construct initial `FVarIdSet` containting free variables ids that have inaccessible user names.
-/
private def getInitialHiddenInaccessible (propOnly : Bool) : MetaM FVarIdSet := do
  let mut r := {}
  for localDecl in (← getLCtx) do
    if localDecl.userName.isInaccessibleUserName then
      if (← pure !propOnly <||> isProp localDecl.type) then
        r := r.insert localDecl.fvarId
  return r

/--
If `pp.inaccessibleNames == false`, then collect two sets of `FVarId`s : `hiddenInaccessible` and `hiddenInaccessibleProp`
1- `hiddenInaccessible` contains `FVarId`s of free variables with inaccessible names that
    a) are not propositions or
    b) are propositions containing "visible" names.
2- `hiddenInaccessibleProp` contains `FVarId`s of free variables with inaccessible names that are propositions
   containing "visible" names.
Both sets do not contain `FVarId`s that contain visible backward or forward dependencies.
The `goalTarget` counts as a forward dependency.

We say a name is visible if it is a free variable with FVarId not in `hiddenInaccessible` nor `hiddenInaccessibleProp`

For propositions in `hiddenInaccessibleProp`, we show only their types when displaying a goal.

Remark: when `pp.inaccessibleNames == true`, we still compute `hiddenInaccessibleProp` to prevent the
goal from being littered with irrelevant names.

-/
def collect (goalTarget : Expr) : MetaM (FVarIdSet × FVarIdSet) := do
  let showLetValues := pp.showLetValues.get (← getOptions)
  if pp.inaccessibleNames.get (← getOptions) then
    -- If `pp.inaccessibleNames == true`, we still must compute `hiddenInaccessibleProp`.
    let hiddenInaccessible ← getInitialHiddenInaccessible (propOnly := true)
    let (_, s) ← fixpoint.run { backwardDeps := false, goalTarget, showLetValues } |>.run { hiddenInaccessible }
    return ({}, s.hiddenInaccessible)
  else
    let hiddenInaccessible ← getInitialHiddenInaccessible (propOnly := false)
    let (_, s) ← fixpoint.run { backwardDeps := true, goalTarget, showLetValues } |>.run { hiddenInaccessible }
    return (s.hiddenInaccessible, s.hiddenInaccessibleProp)

end ToHide

private def addLine (fmt : Format) : Format :=
  if fmt.isNil then fmt else fmt ++ Format.line

def getGoalPrefix (mvarDecl : MetavarDecl) : String :=
  if isLHSGoal? mvarDecl.type |>.isSome then
    -- use special prefix for `conv` goals
    "| "
  else
    "⊢ "

def ppGoal (mvarId : MVarId) : MetaM Format := do
  match (← getMCtx).findDecl? mvarId with
  | none          => return "unknown goal"
  | some mvarDecl =>
    let indent         := 2 -- Use option
    let showLetValues  := pp.showLetValues.get (← getOptions)
    let ppAuxDecls     := pp.auxDecls.get (← getOptions)
    let lctx           := mvarDecl.lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
    withLCtx lctx mvarDecl.localInstances do
      let (hidden, hiddenProp) ← ToHide.collect mvarDecl.type
      -- The followint two `let rec`s are being used to control the generated code size.
      -- Then should be remove after we rewrite the compiler in Lean
      let rec pushPending (ids : List Name) (type? : Option Expr) (fmt : Format) : MetaM Format := do
        if ids.isEmpty then
          return fmt
        else
          let fmt := addLine fmt
          match type? with
          | none      => return fmt
          | some type =>
            let typeFmt ← ppExpr type
            return fmt ++ (Format.joinSep ids.reverse (format " ") ++ " :" ++ Format.nest indent (Format.line ++ typeFmt)).group
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (fmt : Format) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × Format) := do
        if hiddenProp.contains localDecl.fvarId then
          let fmt ← pushPending varNames prevType? fmt
          let fmt  := addLine fmt
          let type ← instantiateMVars localDecl.type
          let typeFmt ← ppExpr type
          let fmt  := fmt ++ ": " ++ typeFmt
          return ([], none, fmt)
        else
          match localDecl with
          | .cdecl _ _ varName type _   =>
            let varName := varName.simpMacroScopes
            let type ← instantiateMVars type
            if prevType? == none || prevType? == some type then
              return (varName :: varNames, some type, fmt)
            else do
              let fmt ← pushPending varNames prevType? fmt
              return ([varName], some type, fmt)
          | .ldecl _ _ varName type val _ => do
            let varName := varName.simpMacroScopes
            let fmt ← pushPending varNames prevType? fmt
            let fmt  := addLine fmt
            let type ← instantiateMVars type
            let typeFmt ← ppExpr type
            let mut fmtElem  := format varName ++ " : " ++ typeFmt
            if showLetValues then
              let val ← instantiateMVars val
              let valFmt ← ppExpr val
              fmtElem := fmtElem ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)
            let fmt := fmt ++ fmtElem.group
            return ([], none, fmt)
      let (varNames, type?, fmt) ← lctx.foldlM (init := ([], none, Format.nil)) fun (varNames, prevType?, fmt) (localDecl : LocalDecl) =>
         if !ppAuxDecls && localDecl.isAuxDecl || hidden.contains localDecl.fvarId then
           return (varNames, prevType?, fmt)
         else
           ppVars varNames prevType? fmt localDecl
      let fmt ← pushPending varNames type? fmt
      let fmt := addLine fmt
      let typeFmt ← ppExpr (← instantiateMVars mvarDecl.type)
      let fmt := fmt ++ getGoalPrefix mvarDecl ++ Format.nest indent typeFmt
      match mvarDecl.userName with
      | Name.anonymous => return fmt
      | name           => return "case " ++ format name.eraseMacroScopes ++ Format.line ++ fmt

end Lean.Meta
