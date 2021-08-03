/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.Parser.Term
import Lean.Data.Lsp.LanguageFeatures
import Lean.Meta.Tactic.Apply
import Lean.Meta.Match.MatcherInfo
import Lean.Server.InfoUtils
import Lean.Parser.Extension

namespace Lean.Server.Completion
open Lsp
open Elab
open Meta

builtin_initialize completionBlackListExt : TagDeclarationExtension ← mkTagDeclarationExtension `blackListCompletion

@[export lean_completion_add_to_black_list]
def addToBlackList (env : Environment) (declName : Name) : Environment :=
  completionBlackListExt.tag env declName

private def isBlackListed (declName : Name) : MetaM Bool := do
  let env ← getEnv
  (declName.isInternal && !isPrivateName declName)
  <||> isAuxRecursor env declName
  <||> isNoConfusion env declName
  <||> isRec declName
  <||> completionBlackListExt.isTagged env declName
  <||> isMatcher declName

private partial def consumeImplicitPrefix (e : Expr) : MetaM Expr := do
  match e with
  | Expr.forallE n d b c =>
    -- We do not consume instance implicit arguments because the user probably wants be aware of this dependency
    if c.binderInfo == BinderInfo.implicit then
      let arg ← mkFreshExprMVar (userName := n) d
      consumeImplicitPrefix (b.instantiate1 arg)
    else
      return e
  | _ => return e

private def isTypeApplicable (type : Expr) (expectedType? : Option Expr) : MetaM Bool :=
  try
    match expectedType? with
    | none => return true
    | some expectedType =>
      let mut (numArgs, hasMVarHead) ← getExpectedNumArgsAux type
      unless hasMVarHead do
        let targetTypeNumArgs ← getExpectedNumArgs expectedType
        numArgs := numArgs - targetTypeNumArgs
      let (newMVars, _, type) ← forallMetaTelescopeReducing type (some numArgs)
      -- TODO take coercions into account
      -- We use `withReducible` to make sure we don't spend too much time unfolding definitions
      -- Alternative: use default and small number of heartbeats
      withReducible <| withoutModifyingState <| isDefEq type expectedType
  catch _ =>
    return false

private def sortCompletionItems (items : Array CompletionItem) : Array CompletionItem :=
  items.qsort fun i1 i2 => i1.label < i2.label

private def mkCompletionItem (label : Name) (type : Expr) : MetaM CompletionItem := do
  let detail ← Meta.ppExpr (← consumeImplicitPrefix type)
  return { label := label.getString!, detail? := some (toString detail), documentation? := none }

structure State where
  itemsMain  : Array CompletionItem := #[]
  itemsOther : Array CompletionItem := #[]

abbrev M := OptionT $ StateRefT State MetaM

private def addCompletionItem (label : Name) (type : Expr) (expectedType? : Option Expr) : M Unit := do
  let item ← mkCompletionItem label type
  if (← isTypeApplicable  type expectedType?) then
    modify fun s => { s with itemsMain := s.itemsMain.push item }
  else
    modify fun s => { s with itemsOther := s.itemsOther.push item }

private def addCompletionItemForDecl (label : Name) (declName : Name) (expectedType? : Option Expr) : M Unit := do
  if let some c ← (← getEnv).find? declName then
    addCompletionItem label c.type expectedType?

private def runM (ctx : ContextInfo) (lctx : LocalContext) (x : M Unit) : IO (Option CompletionList) :=
  ctx.runMetaM lctx do
    match (← x.run |>.run {}) with
    | (none, _) => return none
    | (some _, s) =>
      return some { items := sortCompletionItems s.itemsMain ++ sortCompletionItems s.itemsOther, isIncomplete := true }

private def matchAtomic (id: Name) (declName : Name) : Bool :=
  match id, declName with
  | Name.str Name.anonymous s₁ _, Name.str Name.anonymous s₂ _ => s₁.isPrefixOf s₂
  | _, _ => false

private def normPrivateName (declName : Name) : MetaM Name := do
  match privateToUserName? declName with
  | none => return declName
  | some userName =>
    if mkPrivateName (← getEnv) userName == declName then
      return userName
    else
      return declName

/--
  Return the auto-completion label if `id` can be auto completed using `declName` assuming namespace `ns` is open.
  This function only succeeds with atomic labels. BTW, it seems most clients only use the last part.

  Remark: `danglingDot == true` when the completion point is an identifier followed by `.`.
-/
private def matchDecl? (ns : Name) (id : Name) (danglingDot : Bool) (declName : Name) : MetaM (Option Name) := do
  -- dbg_trace "{ns}, {id}, {declName}, {danglingDot}"
  let declName ← normPrivateName declName
  if !ns.isPrefixOf declName then
    return none
  else
    let declName := declName.replacePrefix ns Name.anonymous
    if id.isPrefixOf declName && danglingDot then
      let declName := declName.replacePrefix id Name.anonymous
      if declName.isAtomic && !declName.isAnonymous then
        return some declName
      else
        return none
    else if !danglingDot then
      match id, declName with
      | Name.str p₁ s₁ _, Name.str p₂ s₂ _ =>
        if p₁ == p₂ && s₁.isPrefixOf s₂ then
          return some s₂
        else
          return none
      | _, _ => none
    else
      return none

private def idCompletionCore (ctx : ContextInfo) (id : Name) (danglingDot : Bool) (expectedType? : Option Expr) : M Unit := do
  let id := id.eraseMacroScopes
  -- dbg_trace ">> id {id} : {expectedType?}"
  if id.isAtomic then
    -- search for matches in the local context
    for localDecl in (← getLCtx) do
      if matchAtomic id localDecl.userName then
        addCompletionItem localDecl.userName localDecl.type expectedType?
  -- search for matches in the environment
  let env ← getEnv
  env.constants.forM fun declName c => do
    unless (← isBlackListed declName) do
      let matchUsingNamespace (ns : Name): M Bool := do
        if let some label ← matchDecl? ns id danglingDot declName then
          -- dbg_trace "matched with {id}, {declName}, {label}"
          addCompletionItem label c.type expectedType?
          return true
        else
          return false
      if (← matchUsingNamespace Name.anonymous) then
        return ()
      -- use current namespace
      let rec visitNamespaces (ns : Name) : M Bool := do
        match ns with
        | Name.str p .. => matchUsingNamespace ns <||> visitNamespaces p
        | _ => return false
      if (← visitNamespaces ctx.currNamespace) then
        return ()
      -- use open decls
      for openDecl in ctx.openDecls do
        match openDecl with
        | OpenDecl.simple ns exs =>
          unless exs.contains declName do
            if (← matchUsingNamespace ns) then
              return ()
        | _ => pure ()
  -- search explicitily open `ids`
  for openDecl in ctx.openDecls do
    match openDecl with
    | OpenDecl.explicit openedId resolvedId =>
      unless (← isBlackListed resolvedId) do
        if matchAtomic id openedId then
          addCompletionItemForDecl openedId resolvedId expectedType?
    | _ => pure ()
  -- search for aliases
  getAliasState env |>.forM fun alias declNames => do
    if matchAtomic id alias then
      declNames.forM fun declName => do
        unless (← isBlackListed declName) do
          addCompletionItemForDecl alias declName expectedType?
  -- TODO search macros
  -- TODO search namespaces

private def idCompletion (ctx : ContextInfo) (lctx : LocalContext) (id : Name) (danglingDot : Bool) (expectedType? : Option Expr) : IO (Option CompletionList) :=
  runM ctx lctx do
    idCompletionCore ctx id danglingDot expectedType?

private def isDotCompletionMethod (typeName : Name) (info : ConstantInfo) : MetaM Bool :=
  forallTelescopeReducing info.type fun xs _ => do
    for x in xs do
      let localDecl ← getLocalDecl x.fvarId!
      let type := localDecl.type.consumeMData
      if type.getAppFn.isConstOf typeName then
        return true
    return false

/--
  Given a type, try to extract relevant type names for dot notation field completion.
  We extract the type name, parent struct names, and unfold the type.
  The process mimics the dot notation elaboration procedure at `App.lean` -/
private partial def getDotCompletionTypeNames (type : Expr) : MetaM NameSet :=
  return (← visit type |>.run {}).2
where
  visit (type : Expr) : StateRefT NameSet MetaM Unit := do
    match type.getAppFn with
    | Expr.const typeName .. =>
      modify fun s => s.insert typeName
      if isStructure (← getEnv) typeName then
        for parentName in getAllParentStructures (← getEnv) typeName do
          modify fun s => s.insert parentName
      let type? ← try unfoldDefinition? type catch _ => pure none
      match type? with
      | some type => visit type
      | none => pure ()
    | _ => pure ()

private def dotCompletion (ctx : ContextInfo) (info : TermInfo) (expectedType? : Option Expr) : IO (Option CompletionList) :=
  runM ctx info.lctx do
    let nameSet ←
      try
        getDotCompletionTypeNames (← instantiateMVars (← inferType info.expr))
      catch _ =>
        pure {}
    if nameSet.isEmpty then
      if info.stx.isIdent then
        idCompletionCore ctx info.stx.getId (danglingDot := false) expectedType?
      else if info.stx.getKind == ``Lean.Parser.Term.completion && info.stx[0].isIdent then
        idCompletionCore ctx info.stx[0].getId (danglingDot := true) expectedType?
      else
        failure
    else
      (← getEnv).constants.forM fun declName c => do
        let typeName := (← normPrivateName declName).getPrefix
        if nameSet.contains typeName then
          unless (← isBlackListed c.name) do
            if (← isDotCompletionMethod typeName c) then
              addCompletionItem c.name.getString! c.type expectedType?

private def optionCompletion (ctx : ContextInfo) (stx : Syntax) : IO (Option CompletionList) :=
  ctx.runMetaM {} do
      let partialName := stx[1].getId
      -- HACK(WN): unfold the type so ForIn works
      let (decls : Std.RBMap _ _ _) ← getOptionDecls
      let opts ← getOptions
      let mut items := #[]
      for ⟨name, decl⟩ in decls do
        if partialName.isPrefixOf name ||
          (match partialName, name with
            | Name.str p₁ s₁ _, Name.str p₂ s₂ _ => p₁ == p₂ && s₁.isPrefixOf s₂
            | _, _ => false) then
          items := items.push
            { label := name.toString
              detail? := s!"({opts.get name decl.defValue}), {decl.descr}"
              documentation? := none }
      return some { items := sortCompletionItems items, isIncomplete := true }

private def tacticCompletion (ctx : ContextInfo) : IO (Option CompletionList) :=
  -- Just return the list of tactics for now.
  ctx.runMetaM {} do
    let table := Parser.getCategory (Parser.parserExtension.getState (← getEnv)).categories `tactic |>.get!.tables.leadingTable
    let items : Array CompletionItem := table.fold (init := #[]) fun items tk parser =>
      -- TODO pretty print tactic syntax
      items.push { label := tk.toString, detail? := none, documentation? := none }
    return some { items := sortCompletionItems items, isIncomplete := true }

partial def find? (fileMap : FileMap) (hoverPos : String.Pos) (infoTree : InfoTree) : IO (Option CompletionList) := do
  let ⟨hoverLine, _⟩ := fileMap.toPosition hoverPos
  match infoTree.foldInfo (init := none) (choose fileMap hoverLine) with
  | some (ctx, Info.ofCompletionInfo info) =>
    match info with
    | CompletionInfo.dot info (expectedType? := expectedType?) .. => dotCompletion ctx info expectedType?
    | CompletionInfo.id stx id danglingDot lctx expectedType? => idCompletion ctx lctx id danglingDot expectedType?
    | CompletionInfo.option stx => optionCompletion ctx stx
    | CompletionInfo.tactic .. => tacticCompletion ctx
    | _ => return none
  | _ =>
    -- TODO try to extract id from `fileMap` and some `ContextInfo` from `InfoTree`
    return none
where
  choose (fileMap : FileMap) (hoverLine : Nat) (ctx : ContextInfo) (info : Info) (best? : Option (ContextInfo × Info)) : Option (ContextInfo × Info) :=
    if !info.isCompletion then best?
    else if let some d := info.occursBefore? hoverPos then
      let pos := info.tailPos?.get!
      let ⟨line, _⟩ := fileMap.toPosition pos
      if line != hoverLine then best?
      else match best? with
        | none => return (ctx, info)
        | some (_, best) =>
          let dBest := best.occursBefore? hoverPos |>.get!
          if d < dBest || (d == dBest && info.isSmaller best) then
            return (ctx, info)
          else
            best?
    else
      best?

end Lean.Server.Completion
