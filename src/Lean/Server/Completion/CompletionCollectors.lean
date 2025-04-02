/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
prelude
import Lean.Data.FuzzyMatching
import Lean.Elab.Tactic.Doc
import Lean.Server.Completion.CompletionResolution
import Lean.Server.Completion.EligibleHeaderDecls
import Lean.Server.RequestCancellation
import Lean.Server.Completion.CompletionUtils

namespace Lean.Server.Completion
open Elab
open Lean.Lsp
open Meta
open FuzzyMatching

section Infrastructure

  private structure Context where
    params            : CompletionParams
    completionInfoPos : Nat


  /-- Intermediate state while completions are being computed. -/
  private structure State where
    /-- All completion items and their fuzzy match scores so far. -/
    items  : Array CompletionItem := #[]

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
      params := ctx.params,
      cPos := ctx.completionInfoPos,
      id?
      : ResolvableCompletionItemData
    }
    let item := { item with data? := toJson data }
    modify fun s => { s with items := s.items.push item }

  /--
  Adds a new completion item with the given `label`, `id`, `kind` and `score` to the state in `M`.
  Computes the doc string from the environment if available.
  -/
  private def addUnresolvedCompletionItem
      (label         : Name)
      (id            : CompletionIdentifier)
      (kind          : CompletionItemKind)
      : M Unit := do
    let env ← getEnv
    let tags? := do
      let .const declName := id
        | none
      guard <| Linter.isDeprecated env declName
      some #[CompletionItemTag.deprecated]
    let item := { label := label.toString, kind? := kind, tags? }
    addItem item id

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
    else if constInfo.isTheorem then
      return CompletionItemKind.event
    else if (← isProjectionFn constInfo.name) then
      return CompletionItemKind.field
    else
      let isFunction : Bool ← withTheReader Core.Context ({ · with maxHeartbeats := 0 }) do
        return (← whnf constInfo.type).isForall
      if isFunction then
        return CompletionItemKind.function
      else
        return CompletionItemKind.constant

  private def addUnresolvedCompletionItemForDecl (label : Name) (declName : Name) : M Unit := do
    if let some c := (← getEnv).find? declName then
      addUnresolvedCompletionItem label (.const declName) (← getCompletionKindForDecl c)

  private def addKeywordCompletionItem (keyword : String) : M Unit := do
    let item := { label := keyword, detail? := "keyword", documentation? := none, kind? := CompletionItemKind.keyword }
    addItem item

  private def addNamespaceCompletionItem (ns : Name) : M Unit := do
    let item := { label := ns.toString, detail? := "namespace", documentation? := none, kind? := CompletionItemKind.module }
    addItem item

  private def runM
      (params            : CompletionParams)
      (completionInfoPos : Nat)
      (ctx               : ContextInfo)
      (lctx              : LocalContext)
      (x                 : M Unit)
      : CancellableM (Array CompletionItem) := do
    let tk ← read
    let r ← ctx.runMetaM lctx do
      x.run ⟨params, completionInfoPos⟩ |>.run {} |>.run tk
    match r with
    | .error _ => throw .requestCancelled
    | .ok (_, s) => return s.items

end Infrastructure

section Utils

  private partial def containsSuccessiveCharacters (a b : String) : Bool :=
    go ⟨0⟩ ⟨0⟩
  where
    go (aPos bPos : String.Pos) : Bool :=
      if ha : a.atEnd aPos then
        true
      else if hb : b.atEnd bPos then
        false
      else
        let ac := a.get' aPos ha
        let bc := b.get' bPos hb
        let bPos := b.next' bPos hb
        if ac == bc then
          let aPos := a.next' aPos ha
          go aPos bPos
        else
          go aPos bPos

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
        if containsSuccessiveCharacters s₁ s₂ then
          return some <| .mkSimple s₂
        else
          return none
      else if p₁.isAnonymous then
        -- If `id` is namespace-less, also fuzzy-match declaration names in arbitrary namespaces
        -- (but don't match the namespace itself).
        -- Penalize score by component length of added namespace.
        if containsSuccessiveCharacters s₁ s₂ then
          return some declName
        else
          return none
    return none

  private def forEligibleDeclsWithCancellationM [Monad m] [MonadEnv m]
      [MonadLiftT (ST IO.RealWorld) m] [MonadCancellable m] [MonadLiftT IO m]
      (f : Name → ConstantInfo → m PUnit) : m PUnit := do
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
      | .str .anonymous s₁, .str .anonymous s₂ => containsSuccessiveCharacters s₁ s₂
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
            (Name.mkStr p (s.extract 0 ⟨newLen - optDot - len⟩), newLen)
    (go id).1

  def matchNamespace (ns : Name) (nsFragment : Name) (danglingDot : Bool) : Bool :=
    if danglingDot then
      if nsFragment != ns && nsFragment.isPrefixOf ns then
        true
      else
        false
    else
      match ns, nsFragment with
      | .str p₁ s₁, .str p₂ s₂ =>
        if p₁ == p₂ then containsSuccessiveCharacters s₂ s₁ else false
      | _, _ => false

  def completeNamespaces (ctx : ContextInfo) (id : Name) (danglingDot : Bool) : M Unit := do
    let env ← getEnv
    let add (ns : Name) (ns' : Name) : M Unit :=
      if danglingDot then
        addNamespaceCompletionItem (ns.replacePrefix (ns' ++ id) Name.anonymous)
      else
        addNamespaceCompletionItem (ns.replacePrefix ns' Name.anonymous)
    env.getNamespaceSet |>.forM fun ns => do
      unless ns.isInternal || env.contains ns do -- Ignore internal and namespaces that are also declaration names
        for openDecl in ctx.openDecls do
          match openDecl with
          | OpenDecl.simple ns' _      =>
            if matchNamespace ns (ns' ++ id) danglingDot then
              add ns ns'
              return ()
          | _ => pure ()
        -- use current namespace
        let rec visitNamespaces (ns' : Name) : M Unit := do
          if matchNamespace ns (ns' ++ id) danglingDot then
            add ns ns'
          else
            match ns' with
            | Name.str p .. => visitNamespaces p
            | _ => return ()
        visitNamespaces ctx.currNamespace

end IdCompletionUtils

section DotCompletionUtils

  /-- Return `true` if `e` is a `declName`-application, or can be unfolded (delta-reduced) to one. -/
  private partial def isDefEqToAppOf (e : Expr) (declName : Name) : MetaM Bool := do
    let isConstOf := match e.getAppFn with
      | .const name .. => (privateToUserName? name).getD name == declName
      | _ => false
    if isConstOf then
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
  Checks whether the expected type of `info.type` can be reduced to an application of `typeName`.
  -/
  private def isDotIdCompletionMethod (typeName : Name) (info : ConstantInfo) : MetaM Bool := do
    forallTelescopeReducing info.type fun _ type =>
      isDefEqToAppOf type.consumeMData typeName

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
  private def NameSetModPrivate := RBTree Name cmpModPrivate

  /--
    Given a type, try to extract relevant type names for dot notation field completion.
    We extract the type name, parent struct names, and unfold the type.
    The process mimics the dot notation elaboration procedure at `App.lean` -/
  private def getDotCompletionTypeNameSet (type : Expr) : MetaM NameSetModPrivate := do
    let mut set := .empty
    for typeName in ← getDotCompletionTypeNames type do
      set := set.insert typeName
    return set

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
        addUnresolvedCompletionItem localDecl.userName (.fvar localDecl.fvarId) (kind := CompletionItemKind.variable)
  -- search for matches in the environment
  let env ← getEnv
  forEligibleDeclsWithCancellationM fun declName c => do
    let bestMatch? ← (·.2) <$> StateT.run (s := none) do
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
    if let some bestLabel := bestMatch? then
      addUnresolvedCompletionItem bestLabel (.const declName) (← getCompletionKindForDecl c)
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
    (params            : CompletionParams)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (lctx              : LocalContext)
    (stx               : Syntax)
    (id                : Name)
    (hoverInfo         : HoverInfo)
    (danglingDot       : Bool)
    : CancellableM (Array CompletionItem) :=
  runM params completionInfoPos ctx lctx do
    idCompletionCore ctx stx id hoverInfo danglingDot

def dotCompletion
    (params            : CompletionParams)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (info              : TermInfo)
    : CancellableM (Array CompletionItem) :=
  runM params completionInfoPos ctx info.lctx do
    let nameSet ← try
      getDotCompletionTypeNameSet (← instantiateMVars (← inferType info.expr))
    catch _ =>
      pure RBTree.empty
    if nameSet.isEmpty then
      return

    forEligibleDeclsWithCancellationM fun declName c => do
      let unnormedTypeName := declName.getPrefix
      if ! nameSet.contains unnormedTypeName then
        return
      let some declName ← normPrivateName? declName
        | return
      let typeName := declName.getPrefix
      if ! (← isDotCompletionMethod typeName c) then
        return
      let completionKind ← getCompletionKindForDecl c
      addUnresolvedCompletionItem (.mkSimple c.name.getString!) (.const c.name) (kind := completionKind)

def dotIdCompletion
    (params            : CompletionParams)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (lctx              : LocalContext)
    (id                : Name)
    (expectedType?     : Option Expr)
    : CancellableM (Array CompletionItem) :=
  runM params completionInfoPos ctx lctx do
    let some expectedType := expectedType?
      | return ()

    let resultTypeFn := (← instantiateMVars expectedType).cleanupAnnotations.getAppFn.cleanupAnnotations
    let .const .. := resultTypeFn
      | return ()

    let nameSet ← try
      getDotCompletionTypeNameSet resultTypeFn
    catch _ =>
      pure RBTree.empty

    forEligibleDeclsWithCancellationM fun declName c => do
      let unnormedTypeName := declName.getPrefix
      if ! nameSet.contains unnormedTypeName then
        return

      let some declName ← normPrivateName? declName
        | return

      let typeName := declName.getPrefix
      if ! (← isDotIdCompletionMethod typeName c) then
        return

      let completionKind ← getCompletionKindForDecl c
      if id.isAnonymous then
        -- We're completing a lone dot => offer all decls of the type
        addUnresolvedCompletionItem (.mkSimple c.name.getString!) (.const c.name) completionKind
        return

      let some label ← matchDecl? typeName id (danglingDot := false) declName | pure ()
      addUnresolvedCompletionItem label (.const c.name) completionKind

def fieldIdCompletion
    (params            : CompletionParams)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (lctx              : LocalContext)
    (id                : Option Name)
    (structName        : Name)
    : CancellableM (Array CompletionItem) :=
  runM params completionInfoPos ctx lctx do
    let idStr := id.map (·.toString) |>.getD ""
    let fieldNames := getStructureFieldsFlattened (← getEnv) structName (includeSubobjectFields := false)
    for fieldName in fieldNames do
      let .str _ fieldName := fieldName | continue
      if ! containsSuccessiveCharacters idStr fieldName then
        continue
      let item := { label := fieldName, detail? := "field", documentation? := none, kind? := CompletionItemKind.field }
      addItem item

def optionCompletion
    (params            : CompletionParams)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    (stx               : Syntax)
    (caps              : ClientCapabilities)
    : IO (Array CompletionItem) :=
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
      if containsSuccessiveCharacters partialName name.toString then
        let textEdit :=
          if !caps.textDocument?.any (·.completion?.any (·.completionItem?.any (·.insertReplaceSupport?.any (·)))) then
            none -- InsertReplaceEdit not supported by client
          else if let some ⟨start, stop⟩ := stx[1].getRange? then
            let stop := if trailingDot then stop + ' ' else stop
            let range := ⟨ctx.fileMap.utf8PosToLspPos start, ctx.fileMap.utf8PosToLspPos stop⟩
            some { newText := name.toString, insert := range, replace := range : InsertReplaceEdit }
          else
            none
        items := items.push {
            label := name.toString
            detail? := s!"({opts.get name decl.defValue}), {decl.descr}"
            documentation? := none,
            kind? := CompletionItemKind.property -- TODO: investigate whether this is the best kind for options.
            textEdit? := textEdit
            data? := toJson {
              params,
              cPos := completionInfoPos,
              id? := none : ResolvableCompletionItemData
            }
          }
    return items

def tacticCompletion
    (params            : CompletionParams)
    (completionInfoPos : Nat)
    (ctx               : ContextInfo)
    : IO (Array CompletionItem) := ctx.runMetaM .empty do
  let allTacticDocs ← Tactic.Doc.allTacticDocs
  let items : Array CompletionItem := allTacticDocs.map fun tacticDoc => {
      label          := tacticDoc.userName
      detail?        := none
      documentation? := tacticDoc.docString.map fun docString =>
        { value := docString, kind := MarkupKind.markdown : MarkupContent }
      kind?          := CompletionItemKind.keyword
      data?          := toJson { params, cPos := completionInfoPos, id? := none : ResolvableCompletionItemData }
    }
  return items

end Lean.Server.Completion
