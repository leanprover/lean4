/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich, Lars König, Wojciech Nawrocki
-/
module

prelude
public import Lean.Server.Utils
public import Lean.Data.Lsp.Internal
public import Lean.Util.CollectFVars
public import Lean.Util.ForEachExpr
meta import Lean.Parser.Module

public section

namespace Lean.Server

open Lsp
open Elab

inductive GoToKind
  | declaration | definition | type
  deriving BEq, ToJson, FromJson

def GoToKind.determineTargetExprs (kind : GoToKind) (ti : TermInfo) : MetaM (Array Expr) := do
  match kind with
  | .type =>
    let type ← instantiateMVars <| ← Meta.inferType ti.expr
    let (_, targetExprs) ← StateT.run (s := #[]) <| type.forEach fun e =>
      match e with
      | .fvar ..
      | .const .. =>
        modify (·.push e)
      | _ =>
        pure ()
    return targetExprs
  | _ =>
    return #[← instantiateMVars ti.expr]

partial def getInstanceProjectionArg? (e : Expr) : MetaM (Option Expr) := do
  let some (e, projInfo) ← Meta.withReducible <| reduceToProjection? e
    | return none
  let instIdx := projInfo.numParams
  let appArgs := e.getAppArgs
  return appArgs[instIdx]?
where
  reduceToProjection? (e : Expr) : MetaM (Option (Expr × ProjectionFunctionInfo)) := do
    let env ← getEnv
    let .const n _ := e.getAppFn'
      | return none
    if let some projInfo := env.getProjectionFnInfo? n then
      return some (e, projInfo)
    -- Unfold reducible definitions when looking for a projection.
    -- For example, this ensures that we get `LT.lt` instance projection entries on `GT.gt`.
    let some e ← Meta.unfoldDefinition? e
      | return none
    reduceToProjection? e

def isInstanceProjection (e : Expr) : MetaM Bool := do
  return (← getInstanceProjectionArg? e).isSome

/-- Checks whether `ti1` is an instance projection info that subsumes `ti2`. -/
def isInstanceProjectionInfoFor (kind : GoToKind) (ti1 ti2 : TermInfo) : MetaM Bool := do
  if kind == .type then
    return false
  let some startPos1 := ti1.stx.getPos? (canonicalOnly := true)
    | return false
  let some startPos2 := ti2.stx.getPos? (canonicalOnly := true)
    | return false
  if startPos1 != startPos2 then
    return false
  let e1 ← instantiateMVars ti1.expr
  let e2 ← instantiateMVars ti2.expr
  if ! (← isInstanceProjection e1) || (← isInstanceProjection e2) then
    return false
  return e1.getAppFn' == e2.getAppFn'

structure GoToContext where
  doc : DocumentMeta
  kind : GoToKind
  infoTree? : Option InfoTree
  originInfo? : Option Info
  children : PersistentArray InfoTree

abbrev GoToM α := ReaderT GoToContext MetaM α

def GoToM.run (ctx : GoToContext) (ci : ContextInfo) (lctx : LocalContext) (act : GoToM α) :
    IO α :=
  ci.runMetaM lctx <| ReaderT.run act ctx

def locationLinksFromDecl (declName : Name) : GoToM (Array LeanLocationLink) := do
  let ctx ← read
  -- Potentially this name is a builtin that has not been imported yet:
  if ! (← getEnv).contains declName then
    return #[]
  let some (declModName, declModUri) ← declMod?
    | return #[]
  let some ranges ← findDeclarationRanges? declName
    | return #[]
  let originSelectionRange? := do
    let i ← ctx.originInfo?
    let r ← i.range?
    return r.toLspRange ctx.doc.text
  let ll : LeanLocationLink := {
    originSelectionRange?
    targetUri := declModUri
    targetRange := ranges.range.toLspRange
    targetSelectionRange := ranges.selectionRange.toLspRange
    ident? := some ⟨declModName, declName.eraseMacroScopes⟩
    isDefault := false
  }
  return #[ll]
where
  declMod? : GoToM (Option (Name × DocumentUri)) := do
    let ctx ← read
    let declMod? ← findModuleOf? declName
    match declMod? with
    | some declModName =>
      let some declModUri ← documentUriFromModule? declModName
        | return none
      return some (declModName, declModUri)
    | none =>
      return some (ctx.doc.mod, ctx.doc.uri)

def locationLinksFromBinder (id : FVarId) : GoToM (Array LeanLocationLink) := do
  let ctx ← read
  let doc := ctx.doc
  let some binderInfo ← binderInfo?
    | return #[]
  let some binderInfoRange := binderInfo.range?
    | return #[]
  let binderInfoRange := binderInfoRange.toLspRange doc.text
  let originSelectionRange? := do
    let i ← ctx.originInfo?
    let r ← i.range?
    return r.toLspRange doc.text
  let ll : LeanLocationLink := {
    originSelectionRange?
    targetUri := doc.uri
    targetRange := binderInfoRange
    targetSelectionRange := binderInfoRange
    ident? := none
    isDefault := false
  }
  return #[ll]
where
  binderInfo? : GoToM (Option Info) := do
    let ctx ← read
    let some infoTree := ctx.infoTree?
      | return none
    return infoTree.findInfo? fun
      | .ofTermInfo { isBinder := true, expr := .fvar id' .., .. } => id' == id
      | _ => false

def locationLinksFromImport (i : CommandInfo) : GoToM (Array LeanLocationLink) := do
  let ctx ← read
  let `(Parser.Module.import| $[public]? $[meta]? import $[all]? $mod) := i.stx
    | return #[]
  let some modUri ← documentUriFromModule? mod.getId
    | return #[]
  let range := { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ : Range }
  let originSelectionRange? := do
    let r ← mod.raw.getRange? (canonicalOnly := true)
    return r.toLspRange ctx.doc.text
  let ll : LeanLocationLink := {
    originSelectionRange?
    targetUri := modUri
    targetRange := range
    targetSelectionRange := range
    ident? := none
    isDefault := false
  }
  return #[ll]

def locationLinksDefault : GoToM (Array LeanLocationLink) := do
  -- If other location link resolutions fail, we try to show the elaborator or parser
  let names ← defaultDeclNames
  let mut ll := #[]
  for name in names do
    ll := ll ++ (← locationLinksFromDecl name)
  return ll.map ({· with isDefault := true})
where
  defaultDeclNames : GoToM (Array Name) := do
    let ctx ← read
    let env ← getEnv
    let some originInfo := ctx.originInfo?
      | return #[]
    let some ei := originInfo.toElabInfo?
      | return #[]
    let e := ei.elaborator
    if e == `Delab then
      return #[]
    if e == `Lean.Elab.Term.elabApp || e == `Lean.Elab.Term.elabIdent then
      return #[]
    let mut names := #[]
    if env.contains e then
      names := names.push e
    if ctx.kind == .declaration && env.contains ei.stx.getKind then
      names := names.push ei.stx.getKind
    return names

def locationLinksFromErrorNameInfo (eni : ErrorNameInfo) : GoToM (Array LeanLocationLink) := do
  let ctx ← read
  let some explan ← getErrorExplanation? eni.errorName
    | return #[]
  let some loc := explan.declLoc?
    | return #[]
  let some modUri ← documentUriFromModule? loc.module
    | return #[]
  let range := loc.range.toLspRange
  let originSelectionRange? := do
    let r ← eni.stx.getRange? (canonicalOnly := true)
    return r.toLspRange ctx.doc.text
  let link : LeanLocationLink := {
    originSelectionRange?
    targetUri := modUri
    targetRange := range
    targetSelectionRange := range
    ident? := none
    isDefault := false
  }
  return #[link]

def locationLinksFromInstanceProjection (e : Expr) : GoToM (Array LeanLocationLink) := do
  -- Go-to-definition on a projection application of a typeclass
  -- should return all instances generated by TC.
  let .const n _ := e.getAppFn.consumeMData
    | return #[]
  let some instArg ← getInstanceProjectionArg? e
    | return #[]
  let mut results := #[]
  for inst in ← extractInstances instArg do
    results := results.append <| ← locationLinksFromDecl inst
  results := results.append <| ← locationLinksFromDecl n
  return results
where
  extractInstances (e : Expr) : GoToM (Array Name) := do
    match e with
    | .const declName _ =>
      if ! (← Lean.Meta.isInstance declName) then
        return #[]
      return #[declName]
    | .app fn arg =>
      let fnInstances ← extractInstances fn
      let argInstances ← extractInstances arg
      return argInstances ++ fnInstances
    | .mdata _ e =>
      extractInstances e
    | _ =>
      return #[]

def locationLinksFromTermInfo (ti : TermInfo) : GoToM (Array LeanLocationLink) := do
  let ctx ← read
  let mut ll := #[]
  let exprs ← ctx.kind.determineTargetExprs ti
  for expr in exprs do
    let newLL ←
      match expr.consumeMData with
      | Expr.const n .. =>
        locationLinksFromDecl n
      | Expr.fvar id .. =>
        locationLinksFromBinder id
      | _ =>
        locationLinksFromInstanceProjection expr
    ll := ll ++ newLL
  return ll

def locationLinksFromDelabTermInfo (dti : DelabTermInfo) : GoToM (Array LeanLocationLink) := do
  let ctx ← read
  let { toTermInfo := ti, location?, .. } := dti
  let some location := location?
    | return ← locationLinksFromTermInfo ti
  let some targetUri ← documentUriFromModule? location.module
    -- If we fail to find a DocumentUri, use the term info so that we have something to jump to.
    | return ← locationLinksFromTermInfo ti
  let range := location.range.toLspRange
  let originSelectionRange? := do
    let r ← Info.ofDelabTermInfo dti |>.range?
    return r.toLspRange ctx.doc.text
  let result : LeanLocationLink := {
    originSelectionRange?
    targetUri
    targetRange := range
    targetSelectionRange := range
    ident? := none
    isDefault := false
  }
  return #[result]

def locationLinksFromFieldInfo (fi : FieldInfo) : GoToM (Array LeanLocationLink) := do
  let ctx ← read
  if ctx.kind != .type then
    return ← locationLinksFromDecl fi.projName
  let expr ← instantiateMVars (← Meta.inferType fi.val)
  let some n := expr.getAppFn.constName?
    | return #[]
  locationLinksFromDecl n

def locationLinksFromOptionInfo (i : OptionInfo) : GoToM (Array LeanLocationLink) :=
  locationLinksFromDecl i.declName

def locationLinksFromCommandInfo (i : CommandInfo) : GoToM (Array LeanLocationLink) := do
  let ctx ← read
  if ! (i matches ⟨`import, _⟩) || ctx.kind == .type then
    return #[]
  locationLinksFromImport i

def locationLinksOfInfo (doc : DocumentMeta) (kind : GoToKind) (ictx : InfoWithCtx)
    (infoTree? : Option InfoTree := none) : IO (Array LeanLocationLink) := do
  let ctx : GoToContext := {
    doc
    kind
    infoTree?
    originInfo? := some ictx.info
    children := ictx.children
  }
  GoToM.run ctx ictx.ctx ictx.info.lctx do
    let ll ←
      match ictx.info with
      | .ofTermInfo ti =>
        locationLinksFromTermInfo ti
      | .ofDelabTermInfo dti =>
        locationLinksFromDelabTermInfo dti
      | .ofFieldInfo fi =>
        locationLinksFromFieldInfo fi
      | .ofOptionInfo oi =>
        locationLinksFromOptionInfo oi
      | .ofCommandInfo cci =>
        locationLinksFromCommandInfo cci
      | .ofErrorNameInfo eni =>
        locationLinksFromErrorNameInfo eni
      | .ofDocElabInfo dei =>
        locationLinksFromDecl dei.name
      | _ =>
        pure #[]
    if kind == .declaration || ll.isEmpty then
      return ll ++ (← locationLinksDefault)
    return ll

end Lean.Server
