/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
module

prelude
public import Lean.Data.FuzzyMatching
public import Lean.Elab.Tactic.Doc
public import Lean.Server.Completion.CompletionResolution
public import Lean.Server.Completion.EligibleHeaderDecls
public import Lean.Server.RequestCancellation

public section

namespace Lean.Server.Completion
open Elab
open Lean.Lsp
open Meta
open FuzzyMatching

section Infrastructure

  private structure Context where
    mod               : Name
    pos               : Lsp.Position
    completionInfoPos : Nat


  /-- Intermediate state while completions are being computed. -/
  private structure State where
    /-- All completion items and their fuzzy match scores so far. -/
    items  : Array ResolvableCompletionItem := #[]

  /--
  Monad used for completion computation that allows modifying a completion `State` and reading
  `CompletionParams`.
  -/
  private abbrev M := ReaderT Context $ StateRefT State $ CancellableT MetaM

  /-- Adds a new completion item to the state in `M`. -/
  private def addItem
      (item  : CompletionItem)
      (id?   : Option CompletionIdentifier := none)
      : M Unit := do
    let ctx ← read
    let data := {
      mod := ctx.mod,
      pos := ctx.pos,
      cPos? := ctx.completionInfoPos,
      id?
      : ResolvableCompletionItemData
    }
    let item := { item with data? := data }
    modify fun s => { s with items := s.items.push item }

  /--
  Adds a new completion item with the given `label`, `id`, `kind` and `score` to the state in `M`.
  Computes the doc string from the environment if available.
  -/
  private def addUnresolvedCompletionItem
      (label         : Name)
      (id            : CompletionIdentifier)
      (kind          : CompletionItemKind)
      (tags          : Array CompletionItemTag)
      : M Unit := do
    let item := { label := label.toString, kind? := kind, tags? := tags }
    addItem item id

  private def addUnresolvedCompletionItemForDecl (label : Name) (declName : Name) : M Unit := do
    if let some c := (← getEnv).find? declName then
      addUnresolvedCompletionItem label (.const declName)
        (← getCompletionKindForDecl c)
        (← getCompletionTagsForDecl declName)

  private def addKeywordCompletionItem (keyword : String) : M Unit := do
    let item := { label := keyword, detail? := "keyword", documentation? := none, kind? := CompletionItemKind.keyword }
    addItem item

  private def addNamespaceCompletionItem (ns : Name) : M Unit := do
    let item := { label := ns.toString, detail? := "namespace", documentation? := none, kind? := CompletionItemKind.module }
    addItem item

  private def runM
      (mod               : Name)
      (pos               : Lsp.Position)
      (completionInfoPos : Nat)
      (ctx               : ContextInfo)
      (lctx              : LocalContext)
      (x                 : M Unit)
      : CancellableM (Array ResolvableCompletionItem) := do
    let tk ← read
    let r ← ctx.runMetaM lctx do
      x.run ⟨mod, pos, completionInfoPos⟩ |>.run {} |>.run tk
    match r with
    | .error _ => throw .requestCancelled
    | .ok (_, s) => return s.items

end Infrastructure

section Utils

  private def normPrivateName? (declName : Name) : MetaM (Option Name) := do
    match privateToUserName? declName with
    | none => return declName
    | some userName =>
      if mkPrivateName (← getEnv) userName == declName then
        return userName
      else
        return none

  /--
    Return the auto-completion label if `id` can be auto completed using `declName` assuming namespace `ns` is open.
    This function only succeeds with atomic labels. BTW, it seems most clients only use the last part.

    Remark: `danglingDot == true` when the completion point is an identifier followed by `.`.
  -/
  private def matchDecl? (ns : Name) (id : Name) (danglingDot : Bool) (declName : Name) : MetaM (Option Name) := do
    let some declName ← normPrivateName? declName
      | return none
    if !ns.isPrefixOf declName then
      return none
    let declName := declName.replacePrefix ns Name.anonymous
    if danglingDot then
      -- If the input is `id.` and `declName` is of the form `id.atomic`, complete with `atomicName`
      if id.isPrefixOf declName then
        let declName := declName.replacePrefix id Name.anonymous
        if declName.isAtomic && !declName.isAnonymous then
          return some declName
    else if let (.str p₁ s₁, .str p₂ s₂) := (id, declName) then
      if p₁ == p₂ then
        -- If the namespaces agree, fuzzy-match on the trailing part
        if s₁.charactersIn s₂ then
          return some <| .mkSimple s₂
        else
          return none
      else if p₁.isAnonymous then
        -- If `id` is namespace-less, also fuzzy-match declaration names in arbitrary namespaces
        -- (but don't match the namespace itself).
        -- Penalize score by component length of added namespace.
        if s₁.charactersIn s₂ then
          return some declName
        else
          return none
    return none

  private def forEligibleDeclsWithCancellationM [Monad m] [MonadEnv m] [MonadLiftT MetaM m]
      [MonadCancellable m] (f : Name → EligibleDecl → m PUnit) : m PUnit := do
    let _ ← StateT.run (s := 0) <| forEligibleDeclsM fun decl ci => do
      modify (· + 1)
      if (← get) >= 10000 then
        RequestCancellation.check
        set <| 0
      f decl ci

end Utils

section IdCompletionUtils

  private def matchAtomic (id : Name) (declName : Name) (danglingDot : Bool) : Bool :=
    if danglingDot then
      false
    else
      match id, declName with
      | .str .anonymous s₁, .str .anonymous s₂ => s₁.charactersIn s₂
      | _, _ => false

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
            (Name.mkStr p (String.Pos.Raw.extract s 0 ⟨newLen - optDot - len⟩), newLen)
    (go id).1

  private def bestLabelForDecl? (ctx : ContextInfo) (declName : Name) (id : Name) (danglingDot : Bool) :
      M (Option Name) := Prod.snd <$> StateT.run (s := none) do
    let matchUsingNamespace (ns : Name) : StateT (Option Name) M Unit := do
      let some label ← matchDecl? ns id danglingDot declName
        | return
      modify fun
        | none =>
          some label
        | some bestLabel =>
          -- for open namespaces `A` and `A.B` and a decl `A.B.c`, pick the decl `c` over `B.c`
          if label.isSuffixOf bestLabel then
            some label
          else
            some bestLabel
    let rec visitNamespaces (ns : Name) : StateT (Option Name) M Unit := do
      let Name.str p .. := ns
        | return ()
      matchUsingNamespace ns
      visitNamespaces p
    -- use current namespace
    visitNamespaces ctx.currNamespace
    -- use open decls
    for openDecl in ctx.openDecls do
      let OpenDecl.simple ns exs := openDecl
        | pure ()
      if exs.contains declName then
        continue
      matchUsingNamespace ns
    matchUsingNamespace Name.anonymous

  private def completeNamespaces (ctx : ContextInfo) (id : Name) (danglingDot : Bool) : M Unit := do
    let env ← getEnv
    env.getNamespaceSet |>.forM fun ns => do
      unless ns.isInternal || env.contains ns do -- Ignore internal and namespaces that are also declaration names
        let label? ← bestLabelForDecl? ctx ns id danglingDot
        if let some bestLabel := label? then
          addNamespaceCompletionItem bestLabel

end IdCompletionUtils

section DotCompletionUtils

  /--
  Converts `n` to `Name.anonymous` if `n` is a private prefix (see `Lean.isPrivatePrefix`).
  -/
  private def stripPrivatePrefix (n : Name) : Name :=
    match n with
    | .num _ 0 => if isPrivatePrefix n then .anonymous else n
    | _ => n

  /--
  Compares `n₁` and `n₂` modulo private prefixes. Similar to `Name.cmp` but ignores all
  private prefixes in both names.
  Necessary because the namespaces of private names do not contain private prefixes.
  -/
  private partial def cmpModPrivate (n₁ n₂ : Name) : Ordering :=
    let n₁ := stripPrivatePrefix n₁
    let n₂ := stripPrivatePrefix n₂
    match n₁, n₂ with
    | .anonymous, .anonymous => Ordering.eq
    | .anonymous, _          => Ordering.lt
    | _,          .anonymous => Ordering.gt
    | .num p₁ i₁, .num p₂ i₂ =>
      match compare i₁ i₂ with
      | Ordering.eq => cmpModPrivate p₁ p₂
      | ord         => ord
    | .num _ _,   .str _ _   => Ordering.lt
    | .str _ _,   .num _ _   => Ordering.gt
    | .str p₁ n₁, .str p₂ n₂ =>
      match compare n₁ n₂ with
      | Ordering.eq => cmpModPrivate p₁ p₂
      | ord         => ord

  /--
  `NameSet` where names are compared according to `cmpModPrivate`.
  Helps speed up dot completion because it allows us to look up names without first having to
  strip the private prefix from deep in the name, letting us reject most names without
  having to scan the full name first.
  -/
  private def NameSetModPrivate := Std.TreeSet Name cmpModPrivate

  private def NameSetModPrivate.ofArray (names : Array Name) : NameSetModPrivate :=
    Std.TreeSet.ofArray names cmpModPrivate

  /--
    Given a type, try to extract relevant type names for dot notation field completion (for `s.f x₁ ... xₙ`).
    We extract the type name, parent struct names, and unfold the type.
    The process mimics the dot notation elaboration procedure at `App.lean` -/
  private def getDotCompletionTypeNameSet (type : Expr) : MetaM NameSetModPrivate := do
    let mut set := .empty
    for typeName in ← getDotCompletionTypeNames type do
      set := set.insert typeName
    return set

  /-- Return `true` if `e` is a `declName`-application, or can be unfolded (delta-reduced) to one. -/
  private partial def isDefEqToAppOf (e : Expr) (declName : Name) : MetaM Bool := do
    let isConstOf := match e.getAppFn with
      | .const name .. => (privateToUserName? name).getD name == declName
      | _ => false
    if isConstOf then
      return true
    let some e ← unfoldDefinitionGuarded? e | return false
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
  Checks whether the type of `info.type` returns one of the type names in `typeNameSet`, for dot ident notation completion.
  The process mimics the dotted identifier notation elaboration procedure at `Lean.Elab.App`.
  -/
  private partial def isDotIdCompletionMethod (typeNameSet : NameSetModPrivate) (info : ConstantInfo) : MetaM Bool := do
    let rec visit (type : Expr) : MetaM Bool := do
      let type ← try whnfCoreUnfoldingAnnotations type catch _ => pure type
      if type.isForall then
        forallTelescope type fun _ type => visit type
      else
        let type ← instantiateMVars type
        let .const typeName _ := type.getAppFn | return false
        if typeNameSet.contains typeName then
          return true
        else if let some type' ← unfoldDefinitionGuarded? type then
          visit type'
        else
          return false
    visit info.type

end DotCompletionUtils

private def idCompletionCore
    (ctx         : ContextInfo)
    (stx         : Syntax)
    (id          : Name)
    (hoverInfo   : HoverInfo)
    (danglingDot : Bool)
    : M Unit := do
  let mut id := id
  if id.hasMacroScopes then
    if stx.getHeadInfo matches .original .. then
      id := id.eraseMacroScopes
    else
      -- Identifier is synthetic and has macro scopes => no completions
      -- Erasing the macro scopes does not make sense in this case because the identifier name
      -- is some random synthetic string.
      return
  let mut danglingDot := danglingDot
  if let HoverInfo.inside delta := hoverInfo then
    id := truncate id delta
    danglingDot := false
  if id.isAtomic then
    -- search for matches in the local context
    for localDecl in (← getLCtx) do
      if matchAtomic id localDecl.userName danglingDot then
        addUnresolvedCompletionItem localDecl.userName (.fvar localDecl.fvarId)
          (kind := CompletionItemKind.variable) (tags := #[])
  -- search for matches in the environment
  let env ← getEnv
  forEligibleDeclsWithCancellationM fun declName decl => do
    let bestMatch? ← bestLabelForDecl? ctx declName id danglingDot
    if let some bestLabel := bestMatch? then
      addUnresolvedCompletionItem bestLabel (.const declName) (← decl.kind) (← decl.tags)
  RequestCancellation.check
  let matchAlias (ns : Name) (alias : Name) : Bool :=
    -- Recall that aliases may not be atomic and include the namespace where they were created.
    if ns.isPrefixOf alias then
      let alias := alias.replacePrefix ns Name.anonymous
      matchAtomic id alias danglingDot
    else
      false
  let eligibleHeaderDecls ← getEligibleHeaderDecls env
  -- Auxiliary function for `alias`
  let addAlias (alias : Name) (declNames : List Name) : M Unit := do
    declNames.forM fun declName => do
      if allowCompletion eligibleHeaderDecls env declName then
        addUnresolvedCompletionItemForDecl (.mkSimple alias.getString!) declName
  -- search explicitly open `ids`
  for openDecl in ctx.openDecls do
    match openDecl with
    | OpenDecl.explicit openedId resolvedId =>
      if allowCompletion eligibleHeaderDecls env resolvedId then
        if matchAtomic id openedId danglingDot then
          addUnresolvedCompletionItemForDecl (.mkSimple openedId.getString!) resolvedId
    | OpenDecl.simple ns _      =>
      getAliasState env |>.forM fun alias declNames => do
        if matchAlias ns alias then
          addAlias alias declNames
  -- search for aliases
  getAliasState env |>.forM fun alias declNames => do
    -- use current namespace
    let rec searchAlias (ns : Name) : M Unit := do
      if matchAlias ns alias then
        addAlias alias declNames
      else
        match ns with
        | Name.str p ..  => searchAlias p
        | _ => return ()
    searchAlias ctx.currNamespace
  -- Search keywords
  if !danglingDot then
    if let .str .anonymous s := id then
      let keywords := Parser.getTokenTable env
      for keyword in keywords.findPrefix s do
        addKeywordCompletionItem keyword
  -- Search namespaces
  completeNamespaces ctx id danglingDot

def idCompletion
    (mod               : Name)
    (pos               : Lsp.Position)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (lctx              : LocalContext)
    (stx               : Syntax)
    (id                : Name)
    (hoverInfo         : HoverInfo)
    (danglingDot       : Bool)
    : CancellableM (Array ResolvableCompletionItem) :=
  runM mod pos completionInfoPos ctx lctx do
    idCompletionCore ctx stx id hoverInfo danglingDot

def dotCompletion
    (mod               : Name)
    (pos               : Lsp.Position)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (info              : TermInfo)
    : CancellableM (Array ResolvableCompletionItem) :=
  runM mod pos completionInfoPos ctx info.lctx do
    let nameSet ← try
      getDotCompletionTypeNameSet (← instantiateMVars (← inferType info.expr))
    catch _ =>
      pure Std.TreeSet.empty
    if nameSet.isEmpty then
      return

    forEligibleDeclsWithCancellationM fun declName decl => do
      let unnormedTypeName := declName.getPrefix
      if ! nameSet.contains unnormedTypeName then
        return
      let some declName ← normPrivateName? declName
        | return
      let c := decl.info
      let typeName := declName.getPrefix
      if ! (← isDotCompletionMethod typeName c) then
        return
      addUnresolvedCompletionItem (.mkSimple c.name.getString!) (.const c.name)
        (← decl.kind) (← decl.tags)

def dotIdCompletion
    (mod               : Name)
    (pos               : Lsp.Position)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (lctx              : LocalContext)
    (id                : Name)
    (expectedType?     : Option Expr)
    : CancellableM (Array ResolvableCompletionItem) :=
  runM mod pos completionInfoPos ctx lctx do
    let some expectedType := expectedType?
      | return ()

    let typeNames ← getDotIdCompletionTypeNames expectedType
    if typeNames.isEmpty then
      return ()

    let nameSet := NameSetModPrivate.ofArray typeNames

    forEligibleDeclsWithCancellationM fun declName decl => do
      let unnormedTypeName := declName.getPrefix
      if ! nameSet.contains unnormedTypeName then
        return

      let some declName ← normPrivateName? declName
        | return

      let c := decl.info
      if ! (← isDotIdCompletionMethod nameSet c) then
        return

      let kind ← decl.kind
      let tags ← decl.tags
      if id.isAnonymous then
        -- We're completing a lone dot => offer all decls of the type
        addUnresolvedCompletionItem (.mkSimple c.name.getString!) (.const c.name) kind tags
        return

      let some label ← matchDecl? declName.getPrefix id (danglingDot := false) declName | pure ()
      addUnresolvedCompletionItem label (.const c.name) kind tags

def fieldIdCompletion
    (mod               : Name)
    (pos               : Lsp.Position)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (lctx              : LocalContext)
    (id                : Option Name)
    (structName        : Name)
    : CancellableM (Array ResolvableCompletionItem) :=
  runM mod pos completionInfoPos ctx lctx do
    let idStr := id.map (·.toString) |>.getD ""
    let fieldNames := getStructureFieldsFlattened (← getEnv) structName (includeSubobjectFields := false)
    for fieldName in fieldNames do
      let .str _ fieldName := fieldName | continue
      if ! idStr.charactersIn fieldName then
        continue
      let item := { label := fieldName, detail? := "field", documentation? := none, kind? := CompletionItemKind.field }
      addItem item

/--
Generate completion items for a syntax object generated by `identWithPartialTrailingDot` given a
known collection of completion candidates. Should only be used in contexts where namespaces do not
affect the set of eligible completion candidates.
-/
private def trailingDotCompletion [ForIn Id Coll (Name × α)]
    (entries : Coll) (stx : Syntax) (caps : ClientCapabilities) (ctx : ContextInfo)
    (mkItem : Name → α → Option InsertReplaceEdit → ResolvableCompletionItem) :
    Array ResolvableCompletionItem := Id.run do
  let (partialName, trailingDot) :=
    match stx.getSubstring? (withLeading := false) (withTrailing := false) with
    | none => ("", false)  -- the `ident` is `missing`, list all options
    | some ss =>
      if !ss.stopPos.atEnd ss.str && ss.stopPos.get ss.str == '.' then
        -- include trailing dot, which is not parsed by `ident`
        (ss.toString ++ ".", true)
      else
        (ss.toString, false)
  let mut items := #[]
  for (name, value) in entries do
    if partialName.charactersIn name.toString then
      let textEdit? :=
        if !caps.textDocument?.any (·.completion?.any (·.completionItem?.any (·.insertReplaceSupport?.any (·)))) then
          none -- InsertReplaceEdit not supported by client
        else if let some ⟨start, stop⟩ := stx.getRange? then
          let stop := if trailingDot then stop + ' ' else stop
          let range := ⟨ctx.fileMap.utf8PosToLspPos start, ctx.fileMap.utf8PosToLspPos stop⟩
          some { newText := name.toString, insert := range, replace := range : InsertReplaceEdit }
        else
          none
      items := items.push (mkItem name value textEdit?)
  return items

def optionCompletion
    (mod               : Name)
    (pos               : Lsp.Position)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (stx               : Syntax)
    (caps              : ClientCapabilities)
    : IO (Array ResolvableCompletionItem) :=
  ctx.runMetaM {} do
    -- HACK(WN): unfold the type so ForIn works
    let (decls : Std.TreeMap _ _ _) ← getOptionDecls
    let opts ← getOptions
    -- `stx` is from `"set_option " >> ident`
    return trailingDotCompletion decls stx[1] caps ctx fun name decl textEdit? => {
      label := name.toString
      detail? := s!"({opts.get name decl.defValue}), {decl.descr}"
      documentation? := none,
      kind? := CompletionItemKind.property -- TODO: investigate whether this is the best kind for options.
      textEdit?
      data? := {
        mod
        pos
        cPos? := completionInfoPos
        id? := none : ResolvableCompletionItemData
      }
    }

def errorNameCompletion
    (mod               : Name)
    (pos               : Lsp.Position)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (partialId         : Syntax)
    (caps              : ClientCapabilities)
    : IO (Array ResolvableCompletionItem) :=
  ctx.runMetaM {} do
    let explanations ← getErrorExplanations
    return trailingDotCompletion explanations partialId caps ctx fun name explan textEdit? => {
      label := name.toString,
      detail? := "error name",
      documentation? := some {
        kind := .markdown,
        value := explan.summaryWithSeverity
      }
      -- TODO: whatever we decide about the kind for options above is also likely relevant here
      kind? := CompletionItemKind.property
      textEdit?
      tags? := explan.metadata.removedVersion?.map fun _ => #[CompletionItemTag.deprecated]
      data? := {
        mod
        pos
        cPos? := completionInfoPos
        id? := none : ResolvableCompletionItemData
      }
    }

def tacticCompletion
    (mod               : Name)
    (pos               : Lsp.Position)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    : IO (Array ResolvableCompletionItem) := ctx.runMetaM .empty do
  -- Don't include tactics that are identified only by their internal parser name
  let allTacticDocs ← Tactic.Doc.allTacticDocs (includeUnnamed := false)
  let items : Array ResolvableCompletionItem := allTacticDocs.map fun tacticDoc => {
      label          := tacticDoc.userName
      detail?        := none
      documentation? := tacticDoc.docString.map fun docString =>
        { value := docString, kind := MarkupKind.markdown : MarkupContent }
      kind?          := CompletionItemKind.keyword
      data?          := { mod, pos, cPos? := completionInfoPos, id? := none : ResolvableCompletionItemData }
    }
  return items

private def findEndSectionCompletionCandidates
    (idComponents : Array String) (scopeNames : Array String) : Array String := Id.run do
  let mut r := #[]
  for i in 0...<scopeNames.size do
    let some partiallyCompletedIdComponent := idComponents[idComponents.size - 1]?
      | r := r.push <| mkCandidate i
        continue
    let some partiallyCompletedScopeName := scopeNames[i + idComponents.size - 1]?
      | continue
    if ! partiallyCompletedIdComponent.charactersIn partiallyCompletedScopeName then
      continue
    let mut isPrefixMatch := true
    for j in 0...<idComponents.size - 1 do
      let some scopeName := scopeNames[i + j]?
        | isPrefixMatch := false
          break
      let idComponent := idComponents[j]!
      if idComponent != scopeName then
        isPrefixMatch := false
        break
    if isPrefixMatch then
      r := r.push <| mkCandidate (i + idComponents.size - 1)
  return r
where
  mkCandidate (idx : Nat) : String :=
    ".".intercalate scopeNames[idx:].toList

def endSectionCompletion
    (mod               : Name)
    (pos               : Lsp.Position)
    (completionInfoPos : Nat)
    (id?               : Option Name)
    (danglingDot       : Bool)
    (scopeNames        : List String)
    : IO (Array ResolvableCompletionItem) := do
  let mut idComponents := id?.map (fun id => id.components.toArray.map (·.toString)) |>.getD #[]
  if danglingDot then
    idComponents := idComponents.push ""
  let scopeNames := scopeNames.toArray.pop.takeWhile (! ·.isEmpty) |>.reverse
  let candidates := findEndSectionCompletionCandidates idComponents scopeNames
  return candidates.map fun candidate => {
    label := candidate
    kind? := CompletionItemKind.module
    data? := {
        mod
        pos
        cPos? := completionInfoPos
        id? := none : ResolvableCompletionItemData
      }
  }

end Lean.Server.Completion
