/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.Parser.Term
import Lean.Data.FuzzyMatching
import Lean.Data.Lsp.LanguageFeatures
import Lean.Data.Lsp.Capabilities
import Lean.Data.Lsp.Utf16
import Lean.Meta.Tactic.Apply
import Lean.Meta.Match.MatcherInfo
import Lean.Server.InfoUtils
import Lean.Parser.Extension

namespace Lean.Server.Completion
open Lsp
open Elab
open Meta
open FuzzyMatching

builtin_initialize completionBlackListExt : TagDeclarationExtension ← mkTagDeclarationExtension

@[export lean_completion_add_to_black_list]
def addToBlackList (env : Environment) (declName : Name) : Environment :=
  completionBlackListExt.tag env declName

private def isBlackListed (declName : Name) : MetaM Bool := do
  let env ← getEnv
  (pure (declName.isInternal && !isPrivateName declName))
  <||> (pure <| isAuxRecursor env declName)
  <||> (pure <| isNoConfusion env declName)
  <||> isRec declName
  <||> (pure <| completionBlackListExt.isTagged env declName)
  <||> isMatcher declName

private partial def consumeImplicitPrefix (e : Expr) (k : Expr → MetaM α) : MetaM α := do
  match e with
  | Expr.forallE n d b c =>
    -- We do not consume instance implicit arguments because the user probably wants be aware of this dependency
    if c == .implicit then
      withLocalDecl n c d fun arg =>
        consumeImplicitPrefix (b.instantiate1 arg) k
    else
      k e
  | _ => k e

private def isTypeApplicable (type : Expr) (expectedType? : Option Expr) : MetaM Bool :=
  try
    match expectedType? with
    | none => return true
    | some expectedType =>
      let mut (numArgs, hasMVarHead) ← getExpectedNumArgsAux type
      unless hasMVarHead do
        let targetTypeNumArgs ← getExpectedNumArgs expectedType
        numArgs := numArgs - targetTypeNumArgs
      let (_, _, type) ← forallMetaTelescopeReducing type (some numArgs)
      -- TODO take coercions into account
      -- We use `withReducible` to make sure we don't spend too much time unfolding definitions
      -- Alternative: use default and small number of heartbeats
      withReducible <| withoutModifyingState <| isDefEq type expectedType
  catch _ =>
    return false

private def sortCompletionItems (items : Array (CompletionItem × Float)) : Array CompletionItem :=
  items.qsort (fun (i1, s1) (i2, s2) => if s1 == s2 then i1.label < i2.label else s1 > s2) |>.map (·.1)

private def mkCompletionItem (label : Name) (type : Expr) (docString? : Option String) (kind : CompletionItemKind) : MetaM CompletionItem := do
  let doc? := docString?.map fun docString => { value := docString, kind := MarkupKind.markdown : MarkupContent }
  let detail ← consumeImplicitPrefix type fun type => return toString (← Meta.ppExpr type)
  return { label := label.getString!, detail? := detail, documentation? := doc?, kind? := kind }

structure State where
  itemsMain  : Array (CompletionItem × Float) := #[]
  itemsOther : Array (CompletionItem × Float) := #[]

abbrev M := OptionT $ StateRefT State MetaM

private def addCompletionItem (label : Name) (type : Expr) (expectedType? : Option Expr) (declName? : Option Name) (kind : CompletionItemKind) (score : Float) : M Unit := do
  let docString? ← if let some declName := declName? then findDocString? (← getEnv) declName else pure none
  let item ← mkCompletionItem label type docString? kind
  if (← isTypeApplicable  type expectedType?) then
    modify fun s => { s with itemsMain := s.itemsMain.push (item, score) }
  else
    modify fun s => { s with itemsOther := s.itemsOther.push (item, score) }

private def getCompletionKindForDecl (constInfo : ConstantInfo) : M CompletionItemKind := do
  let env ← getEnv
  if constInfo.isCtor then
    return CompletionItemKind.constructor
  else if constInfo.isInductive then
    if isClass env constInfo.name then
      return CompletionItemKind.class
    else if (← isEnumType constInfo.name) then
      return CompletionItemKind.enum
    else
      return CompletionItemKind.struct
  else if (← isProjectionFn constInfo.name) then
    return CompletionItemKind.field
  else if (← whnf constInfo.type).isForall then
    return CompletionItemKind.function
  else
    return CompletionItemKind.constant

private def addCompletionItemForDecl (label : Name) (declName : Name) (expectedType? : Option Expr) (score : Float) : M Unit := do
  if let some c := (← getEnv).find? declName then
    addCompletionItem label c.type expectedType? (some declName) (← getCompletionKindForDecl c) score

private def addKeywordCompletionItem (keyword : String) : M Unit := do
  let item := { label := keyword, detail? := "keyword", documentation? := none, kind? := CompletionItemKind.keyword }
  modify fun s => { s with itemsMain := s.itemsMain.push (item, 1) }

private def addNamespaceCompletionItem (ns : Name) (score : Float) : M Unit := do
  let item := { label := ns.toString, detail? := "namespace", documentation? := none, kind? := CompletionItemKind.module }
  modify fun s => { s with itemsMain := s.itemsMain.push (item, score) }

private def runM (ctx : ContextInfo) (lctx : LocalContext) (x : M Unit) : IO (Option CompletionList) :=
  ctx.runMetaM lctx do
    match (← x.run |>.run {}) with
    | (none, _) => return none
    | (some _, s) =>
      return some { items := sortCompletionItems s.itemsMain ++ sortCompletionItems s.itemsOther, isIncomplete := true }

private def matchAtomic (id : Name) (declName : Name) : Option Float :=
  match id, declName with
  | .str .anonymous s₁, .str .anonymous s₂ => fuzzyMatchScoreWithThreshold? s₁ s₂
  | _, _ => none

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
private def matchDecl? (ns : Name) (id : Name) (danglingDot : Bool) (declName : Name) : MetaM (Option (Name × Float)) := do
  -- dbg_trace "{ns}, {id}, {declName}, {danglingDot}"
  let declName ← normPrivateName declName
  if !ns.isPrefixOf declName then
    return none
  else
    let declName := declName.replacePrefix ns Name.anonymous
    if id.isPrefixOf declName && danglingDot then
      let declName := declName.replacePrefix id Name.anonymous
      if declName.isAtomic && !declName.isAnonymous then
        return some (declName, 1)
      else
        return none
    else if !danglingDot then
      match id, declName with
      | .str p₁ s₁, .str p₂ s₂ =>
        if p₁ == p₂  then
          return fuzzyMatchScoreWithThreshold? s₁ s₂ |>.map (s₂, ·)
        else
          return none
      | _, _ => return none
    else
      return none

/--
  Truncate the given identifier and make sure it has length `≤ newLength`.
  This function assumes `id` does not contain `Name.num` constructors.
-/
private partial def truncate (id : Name) (newLen : Nat) : Name :=
  let rec go (id : Name) : Name × Nat :=
     match id with
     | Name.anonymous => (id, 0)
     | Name.num ..    => unreachable!
     | .str p s =>
       let (p', len) := go p
       if len + 1 >= newLen then
         (p', len)
       else
         let optDot := if p.isAnonymous then 0 else 1
         let len'   := len + optDot + s.length
         if len' ≤ newLen then
           (id, len')
         else
           (Name.mkStr p (s.extract 0 ⟨newLen - optDot - len⟩), newLen)
  (go id).1

inductive HoverInfo where
  | after
  | inside (delta : Nat)

def matchNamespace (ns : Name) (nsFragment : Name) (danglingDot : Bool) : Option Float :=
  if danglingDot then
    if nsFragment != ns && nsFragment.isPrefixOf ns then
      some 1
    else
      none
  else
    match ns, nsFragment with
    | .str p₁ s₁, .str p₂ s₂ =>
      if p₁ == p₂ then fuzzyMatchScoreWithThreshold? s₂ s₁ else none
    | _, _ => none

def completeNamespaces (ctx : ContextInfo) (id : Name) (danglingDot : Bool) : M Unit := do
  let env ← getEnv
  let add (ns : Name) (ns' : Name) (score : Float) : M Unit :=
    if danglingDot then
      addNamespaceCompletionItem (ns.replacePrefix (ns' ++ id) Name.anonymous) score
    else
      addNamespaceCompletionItem (ns.replacePrefix ns' Name.anonymous) score
  env.getNamespaceSet |>.forM fun ns => do
    unless ns.isInternal || env.contains ns do -- Ignore internal and namespaces that are also declaration names
      for openDecl in ctx.openDecls do
        match openDecl with
        | OpenDecl.simple ns' _      =>
          if let some score := matchNamespace ns (ns' ++ id) danglingDot then
            add ns ns' score
            return ()
        | _ => pure ()
      -- use current namespace
      let rec visitNamespaces (ns' : Name) : M Unit := do
        if let some score := matchNamespace ns (ns' ++ id) danglingDot then
          add ns ns' score
        else
          match ns' with
          | Name.str p .. => visitNamespaces p
          | _ => return ()
      visitNamespaces ctx.currNamespace

private def idCompletionCore (ctx : ContextInfo) (id : Name) (hoverInfo : HoverInfo) (danglingDot : Bool) (expectedType? : Option Expr) : M Unit := do
  let mut id := id.eraseMacroScopes
  let mut danglingDot := danglingDot
  if let HoverInfo.inside delta := hoverInfo then
    id := truncate id delta
    danglingDot := false
  -- dbg_trace ">> id {id} : {expectedType?}"
  if id.isAtomic then
    -- search for matches in the local context
    for localDecl in (← getLCtx) do
      if let some score := matchAtomic id localDecl.userName then
        addCompletionItem localDecl.userName localDecl.type expectedType? none (kind := CompletionItemKind.variable) score
  -- search for matches in the environment
  let env ← getEnv
  env.constants.forM fun declName c => do
    unless (← isBlackListed declName) do
      let matchUsingNamespace (ns : Name): M Bool := do
        if let some (label, score) ← matchDecl? ns id danglingDot declName then
          -- dbg_trace "matched with {id}, {declName}, {label}"
          addCompletionItem label c.type expectedType? declName (← getCompletionKindForDecl c) score
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
  -- Recall that aliases may not be atomic and include the namespace where they were created.
  let matchAlias (ns : Name) (alias : Name) : Option Float :=
    if ns.isPrefixOf alias then
      matchAtomic id (alias.replacePrefix ns Name.anonymous)
    else
      none
  -- Auxiliary function for `alias`
  let addAlias (alias : Name) (declNames : List Name) (score : Float) : M Unit := do
    declNames.forM fun declName => do
      unless (← isBlackListed declName) do
        addCompletionItemForDecl alias declName expectedType? score
  -- search explicitily open `ids`
  for openDecl in ctx.openDecls do
    match openDecl with
    | OpenDecl.explicit openedId resolvedId =>
      unless (← isBlackListed resolvedId) do
        if let some score := matchAtomic id openedId then
          addCompletionItemForDecl openedId resolvedId expectedType? score
    | OpenDecl.simple ns _      =>
      getAliasState env |>.forM fun alias declNames => do
        if let some score := matchAlias ns alias then
          addAlias alias declNames score
  -- search for aliases
  getAliasState env |>.forM fun alias declNames => do
    -- use current namespace
    let rec searchAlias (ns : Name) : M Unit := do
      if let some score := matchAlias ns alias then
        addAlias alias declNames score
      else
        match ns with
        | Name.str p ..  => searchAlias p
        | _ => return ()
    searchAlias ctx.currNamespace
  -- Search keywords
  if let .str .anonymous s := id then
    let keywords := Parser.getTokenTable env
    for keyword in keywords.findPrefix s do
      addKeywordCompletionItem keyword
  -- Search namespaces
  completeNamespaces ctx id danglingDot

private def idCompletion (ctx : ContextInfo) (lctx : LocalContext) (id : Name) (hoverInfo : HoverInfo) (danglingDot : Bool) (expectedType? : Option Expr) : IO (Option CompletionList) :=
  runM ctx lctx do
    idCompletionCore ctx id hoverInfo danglingDot expectedType?

private def unfoldeDefinitionGuarded? (e : Expr) : MetaM (Option Expr) :=
  try unfoldDefinition? e catch _ => pure none

/-- Return `true` if `e` is a `declName`-application, or can be unfolded (delta-reduced) to one. -/
private partial def isDefEqToAppOf (e : Expr) (declName : Name) : MetaM Bool := do
  if e.getAppFn.isConstOf declName then
    return true
  let some e ← unfoldeDefinitionGuarded? e | return false
  isDefEqToAppOf e declName

private def isDotCompletionMethod (typeName : Name) (info : ConstantInfo) : MetaM Bool :=
  forallTelescopeReducing info.type fun xs _ => do
    for x in xs do
      let localDecl ← x.fvarId!.getDecl
      let type := localDecl.type.consumeMData
      if (← isDefEqToAppOf type typeName) then
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
    let .const typeName _ := type.getAppFn | return ()
    modify fun s => s.insert typeName
    if isStructure (← getEnv) typeName then
      for parentName in getAllParentStructures (← getEnv) typeName do
        modify fun s => s.insert parentName
    let some type ← unfoldeDefinitionGuarded? type | return ()
    visit type

private def dotCompletion (ctx : ContextInfo) (info : TermInfo) (hoverInfo : HoverInfo) (expectedType? : Option Expr) : IO (Option CompletionList) :=
  runM ctx info.lctx do
    let nameSet ← try
      getDotCompletionTypeNames (← instantiateMVars (← inferType info.expr))
    catch _ =>
      pure {}
    if nameSet.isEmpty then
      if info.stx.isIdent then
        idCompletionCore ctx info.stx.getId hoverInfo (danglingDot := false) expectedType?
      else if info.stx.getKind == ``Lean.Parser.Term.completion && info.stx[0].isIdent then
        -- TODO: truncation when there is a dangling dot
        idCompletionCore ctx info.stx[0].getId HoverInfo.after (danglingDot := true) expectedType?
      else
        failure
    else
      (← getEnv).constants.forM fun declName c => do
        let typeName := (← normPrivateName declName).getPrefix
        if nameSet.contains typeName then
          unless (← isBlackListed c.name) do
            if (← isDotCompletionMethod typeName c) then
              addCompletionItem c.name.getString! c.type expectedType? c.name (kind := (← getCompletionKindForDecl c)) 1

private def dotIdCompletion (ctx : ContextInfo) (lctx : LocalContext) (id : Name) (expectedType? : Option Expr) : IO (Option CompletionList) :=
  runM ctx lctx do
    let some expectedType := expectedType? | return ()
    let resultTypeFn := (← instantiateMVars expectedType).cleanupAnnotations.getAppFn
    let .const typeName .. := resultTypeFn.cleanupAnnotations | return ()
    (← getEnv).constants.forM fun declName c => do
      let some (label, score) ← matchDecl? typeName id (danglingDot := false) declName | pure ()
      addCompletionItem label c.type expectedType? declName (← getCompletionKindForDecl c) score

private def fieldIdCompletion (ctx : ContextInfo) (lctx : LocalContext) (id : Name) (structName : Name) : IO (Option CompletionList) :=
  runM ctx lctx do
    let idStr := id.toString
    let fieldNames := getStructureFieldsFlattened (← getEnv) structName (includeSubobjectFields := false)
    for fieldName in fieldNames do
      let .str _ fieldName := fieldName | continue
      let some score := fuzzyMatchScoreWithThreshold? idStr fieldName | continue
      let item := { label := fieldName, detail? := "field", documentation? := none, kind? := CompletionItemKind.field }
      modify fun s => { s with itemsMain := s.itemsMain.push (item, score) }

private def optionCompletion (ctx : ContextInfo) (stx : Syntax) (caps : ClientCapabilities) : IO (Option CompletionList) :=
  ctx.runMetaM {} do
    let (partialName, trailingDot) :=
      -- `stx` is from `"set_option" >> ident`
      match stx[1].getSubstring? (withLeading := false) (withTrailing := false) with
      | none => ("", false)  -- the `ident` is `missing`, list all options
      | some ss =>
        if !ss.str.atEnd ss.stopPos && ss.str.get ss.stopPos == '.' then
          -- include trailing dot, which is not parsed by `ident`
          (ss.toString ++ ".", true)
        else
          (ss.toString, false)
    -- HACK(WN): unfold the type so ForIn works
    let (decls : RBMap _ _ _) ← getOptionDecls
    let opts ← getOptions
    let mut items := #[]
    for ⟨name, decl⟩ in decls do
      if let some score := fuzzyMatchScoreWithThreshold? partialName name.toString then
        let textEdit :=
          if !caps.textDocument?.any (·.completion?.any (·.completionItem?.any (·.insertReplaceSupport?.any (·)))) then
            none -- InsertReplaceEdit not supported by client
          else if let some ⟨start, stop⟩ := stx[1].getRange? then
            let stop := if trailingDot then stop + ' ' else stop
            let range := ⟨ctx.fileMap.utf8PosToLspPos start, ctx.fileMap.utf8PosToLspPos stop⟩
            some { newText := name.toString, insert := range, replace := range : InsertReplaceEdit }
          else
            none
        items := items.push
          ({ label := name.toString
             detail? := s!"({opts.get name decl.defValue}), {decl.descr}"
             documentation? := none,
             kind? := CompletionItemKind.property -- TODO: investigate whether this is the best kind for options.
             textEdit? := textEdit }, score)
    return some { items := sortCompletionItems items, isIncomplete := true }

private def tacticCompletion (ctx : ContextInfo) : IO (Option CompletionList) :=
  -- Just return the list of tactics for now.
  ctx.runMetaM {} do
    let table := Parser.getCategory (Parser.parserExtension.getState (← getEnv)).categories `tactic |>.get!.tables.leadingTable
    let items : Array (CompletionItem × Float) := table.fold (init := #[]) fun items tk _ =>
      -- TODO pretty print tactic syntax
      items.push ({ label := tk.toString, detail? := none, documentation? := none, kind? := CompletionItemKind.keyword }, 1)
    return some { items := sortCompletionItems items, isIncomplete := true }

partial def find? (fileMap : FileMap) (hoverPos : String.Pos) (infoTree : InfoTree) (caps : ClientCapabilities) : IO (Option CompletionList) := do
  let ⟨hoverLine, _⟩ := fileMap.toPosition hoverPos
  match infoTree.foldInfo (init := none) (choose fileMap hoverLine) with
  | some (hoverInfo, ctx, Info.ofCompletionInfo info) =>
    match info with
    | .dot info (expectedType? := expectedType?) .. => dotCompletion ctx info hoverInfo expectedType?
    | .id _   id danglingDot lctx expectedType? => idCompletion ctx lctx id hoverInfo danglingDot expectedType?
    | .dotId _  id lctx expectedType? => dotIdCompletion ctx lctx id expectedType?
    | .fieldId _ id lctx structName => fieldIdCompletion ctx lctx id structName
    | .option stx => optionCompletion ctx stx caps
    | .tactic .. => tacticCompletion ctx
    | _ => return none
  | _ =>
    -- TODO try to extract id from `fileMap` and some `ContextInfo` from `InfoTree`
    return none
where
  choose (fileMap : FileMap) (hoverLine : Nat) (ctx : ContextInfo) (info : Info) (best? : Option (HoverInfo × ContextInfo × Info)) : Option (HoverInfo × ContextInfo × Info) :=
    if !info.isCompletion then best?
    else if info.occursInside? hoverPos |>.isSome then
      let headPos          := info.pos?.get!
      let ⟨headPosLine, _⟩ := fileMap.toPosition headPos
      let ⟨tailPosLine, _⟩ := fileMap.toPosition info.tailPos?.get!
      if headPosLine != hoverLine || headPosLine != tailPosLine then
        best?
      else match best? with
        | none                         => (HoverInfo.inside (hoverPos - headPos).byteIdx, ctx, info)
        | some (HoverInfo.after, _, _) => (HoverInfo.inside (hoverPos - headPos).byteIdx, ctx, info)
        | some (_, _, best) =>
          if info.isSmaller best then
            (HoverInfo.inside (hoverPos - headPos).byteIdx, ctx, info)
          else
            best?
    else if let some (HoverInfo.inside _, _, _) := best? then
      -- We assume the "inside matches" have precedence over "before ones".
      best?
    else if let some d := info.occursBefore? hoverPos then
      let pos := info.tailPos?.get!
      let ⟨line, _⟩ := fileMap.toPosition pos
      if line != hoverLine then best?
      else match best? with
        | none => (HoverInfo.after, ctx, info)
        | some (_, _, best) =>
          let dBest := best.occursBefore? hoverPos |>.get!
          if d < dBest || (d == dBest && info.isSmaller best) then
            (HoverInfo.after, ctx, info)
          else
            best?
    else
      best?

end Lean.Server.Completion
