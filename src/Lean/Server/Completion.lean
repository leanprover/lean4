/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment
import Lean.Parser.Term
import Lean.Data.FuzzyMatching
import Lean.Data.Lsp.LanguageFeatures
import Lean.Data.Lsp.Capabilities
import Lean.Data.Lsp.Utf16
import Lean.Meta.CompletionName
import Lean.Meta.Tactic.Apply
import Lean.Meta.Match.MatcherInfo
import Lean.Elab.Tactic.Doc
import Lean.Server.InfoUtils
import Lean.Parser.Extension
import Lean.Server.FileSource
import Lean.Server.CompletionItemData

private partial def Lean.Server.Completion.consumeImplicitPrefix (e : Expr) (k : Expr → MetaM α) : MetaM α := do
  match e with
  | Expr.forallE n d b c =>
    -- We do not consume instance implicit arguments because the user probably wants be aware of this dependency
    if c == .implicit then
      Meta.withLocalDecl n c d fun arg =>
        consumeImplicitPrefix (b.instantiate1 arg) k
    else
      k e
  | _ => k e

namespace Lean.Lsp

/--
Identifier that is sent from the server to the client as part of the `CompletionItem.data?` field.
Needed to resolve the `CompletionItem` when the client sends a `completionItem/resolve` request
for that item, again containing the `data?` field provided by the server.
-/
inductive CompletionIdentifier where
  | const (declName : Name)
  | fvar  (id       : FVarId)
  deriving FromJson, ToJson

/--
`CompletionItemData` that also contains a `CompletionIdentifier`.
See the documentation of`CompletionItemData` and `CompletionIdentifier`.
-/
structure CompletionItemDataWithId extends CompletionItemData where
  id?    : Option CompletionIdentifier
  deriving FromJson, ToJson

/--
Fills the `CompletionItem.detail?` field of `item` using the pretty-printed type identified by `id`.
-/
def CompletionItem.resolve
    (item : CompletionItem)
    (id   : CompletionIdentifier)
    : MetaM CompletionItem := do
  let env ← getEnv
  let lctx ← getLCtx
  let mut item := item

  if item.detail?.isNone then
    let type? := match id with
      | .const declName =>
        env.find? declName |>.map ConstantInfo.type
      | .fvar id =>
        lctx.find? id |>.map LocalDecl.type
    let detail? ← type?.mapM fun type =>
      Lean.Server.Completion.consumeImplicitPrefix type fun typeWithoutImplicits =>
        return toString (← Meta.ppExpr typeWithoutImplicits)
    item := { item with detail? := detail? }

  return item

end Lean.Lsp

namespace Lean.Server.Completion
open Lsp
open Elab
open Meta
open FuzzyMatching

abbrev EligibleHeaderDecls := Std.HashMap Name ConstantInfo

/-- Cached header declarations for which `allowCompletion headerEnv decl` is true. -/
builtin_initialize eligibleHeaderDeclsRef : IO.Ref (Option EligibleHeaderDecls) ←
  IO.mkRef none

/--
Returns the declarations in the header for which `allowCompletion env decl` is true, caching them
if not already cached.
-/
def getEligibleHeaderDecls (env : Environment) : IO EligibleHeaderDecls := do
  eligibleHeaderDeclsRef.modifyGet fun
    | some eligibleHeaderDecls => (eligibleHeaderDecls, some eligibleHeaderDecls)
    | none =>
      let (_, eligibleHeaderDecls) :=
        StateT.run (m := Id) (s := {}) do
          -- `map₁` are the header decls
          env.constants.map₁.forM fun declName c => do
            modify fun eligibleHeaderDecls =>
              if allowCompletion env declName then
                eligibleHeaderDecls.insert declName c
              else
                eligibleHeaderDecls
      (eligibleHeaderDecls, some eligibleHeaderDecls)

/-- Iterate over all declarations that are allowed in completion results. -/
private def forEligibleDeclsM [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m]
    [MonadLiftT IO m] (f : Name → ConstantInfo → m PUnit) : m PUnit := do
  let env ← getEnv
  (← getEligibleHeaderDecls env).forM f
  -- map₂ are exactly the local decls
  env.constants.map₂.forM fun name c => do
    if allowCompletion env name then
      f name c

/-- Checks whether this declaration can appear in completion results. -/
private def allowCompletion (eligibleHeaderDecls : EligibleHeaderDecls) (env : Environment)
    (declName : Name) : Bool :=
  eligibleHeaderDecls.contains declName ||
    env.constants.map₂.contains declName && Lean.Meta.allowCompletion env declName

/--
Sorts `items` descendingly according to their score and ascendingly according to their label
for equal scores.
-/
private def sortCompletionItems (items : Array (CompletionItem × Float)) : Array CompletionItem :=
  let items := items.qsort fun (i1, s1) (i2, s2) =>
    if s1 != s2 then
      s1 > s2
    else
      i1.label.map (·.toLower) < i2.label.map (·.toLower)
  items.map (·.1)

/-- Intermediate state while completions are being computed. -/
structure State where
  /-- All completion items and their fuzzy match scores so far. -/
  items  : Array (CompletionItem × Float) := #[]

/--
Monad used for completion computation that allows modifying a completion `State` and reading
`CompletionParams`.
-/
abbrev M := OptionT $ ReaderT CompletionParams $ StateRefT State MetaM

/-- Adds a new completion item to the state in `M`. -/
private def addItem
    (item  : CompletionItem)
    (score : Float)
    (id?   : Option CompletionIdentifier := none)
    : M Unit := do
  let params ← read
  let data := { params, id? : CompletionItemDataWithId }
  let item := { item with data? := toJson data }
  modify fun s => { s with items := s.items.push (item, score) }

/--
Adds a new completion item with the given `label`, `id`, `kind` and `score` to the state in `M`.
Computes the doc string from the environment if available.
-/
private def addUnresolvedCompletionItem
    (label         : Name)
    (id            : CompletionIdentifier)
    (kind          : CompletionItemKind)
    (score         : Float)
    : M Unit := do
  let env ← getEnv
  let (docStringPrefix?, tags?) := Id.run do
    let .const declName := id
      | (none, none)
    let some param := Linter.deprecatedAttr.getParam? env declName
      | (none, none)
    let docstringPrefix :=
      if let some text := param.text? then
        text
      else if let some newName := param.newName? then
        s!"`{declName}` has been deprecated, use `{newName}` instead."
      else
        s!"`{declName}` has been deprecated."
    (some docstringPrefix, some #[CompletionItemTag.deprecated])
  let docString? ← do
    let .const declName := id
      | pure none
    findDocString? env declName
  let doc? := do
    let docValue ←
      match docStringPrefix?, docString? with
      | none,                 none           => none
      | some docStringPrefix, none           => docStringPrefix
      | none,                 docString      => docString
      | some docStringPrefix, some docString => s!"{docStringPrefix}\n\n{docString}"
    pure { value := docValue , kind := MarkupKind.markdown : MarkupContent }
  let item := { label := label.toString, kind? := kind, documentation? := doc?, tags?}
  addItem item score id

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

private def addUnresolvedCompletionItemForDecl (label : Name) (declName : Name) (score : Float) : M Unit := do
  if let some c := (← getEnv).find? declName then
    addUnresolvedCompletionItem label (.const declName) (← getCompletionKindForDecl c) score

private def addKeywordCompletionItem (keyword : String) (score : Float) : M Unit := do
  let item := { label := keyword, detail? := "keyword", documentation? := none, kind? := CompletionItemKind.keyword }
  addItem item score

private def addNamespaceCompletionItem (ns : Name) (score : Float) : M Unit := do
  let item := { label := ns.toString, detail? := "namespace", documentation? := none, kind? := CompletionItemKind.module }
  addItem item score

private def runM (params : CompletionParams) (ctx : ContextInfo) (lctx : LocalContext) (x : M Unit)
    : IO (Option CompletionList) :=
  ctx.runMetaM lctx do
    match (← x.run |>.run params |>.run {}) with
    | (none, _) => return none
    | (some _, s) =>
      return some { items := sortCompletionItems s.items, isIncomplete := true }

private def matchAtomic (id : Name) (declName : Name) : Option Float :=
  match id, declName with
  | .str .anonymous s₁, .str .anonymous s₂ => fuzzyMatchScoreWithThreshold? s₁ s₂
  | _, _ => none

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
private def matchDecl? (ns : Name) (id : Name) (danglingDot : Bool) (declName : Name) : MetaM (Option (Name × Float)) := do
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
        return some (declName, 1)
  else if let (.str p₁ s₁, .str p₂ s₂) := (id, declName) then
    if p₁ == p₂ then
      -- If the namespaces agree, fuzzy-match on the trailing part
      return fuzzyMatchScoreWithThreshold? s₁ s₂ |>.map (.mkSimple s₂, ·)
    else if p₁.isAnonymous then
      -- If `id` is namespace-less, also fuzzy-match declaration names in arbitrary namespaces
      -- (but don't match the namespace itself).
      -- Penalize score by component length of added namespace.
      return fuzzyMatchScoreWithThreshold? s₁ s₂ |>.map (declName, · / (p₂.getNumParts + 1).toFloat)
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
      if let some score := matchAtomic id localDecl.userName then
        addUnresolvedCompletionItem localDecl.userName (.fvar localDecl.fvarId) (kind := CompletionItemKind.variable) score
  -- search for matches in the environment
  let env ← getEnv
  forEligibleDeclsM fun declName c => do
    let bestMatch? ← (·.2) <$> StateT.run (s := none) do
      let matchUsingNamespace (ns : Name) : StateT (Option (Name × Float)) M Unit := do
        let some (label, score) ← matchDecl? ns id danglingDot declName
          | return
        modify fun
          | none =>
            some (label, score)
          | some (bestLabel, bestScore) =>
            -- for open namespaces `A` and `A.B` and a decl `A.B.c`, pick the decl `c` over `B.c`
            if label.isSuffixOf bestLabel then
              some (label, score)
            else
              some (bestLabel, bestScore)
      let rec visitNamespaces (ns : Name) : StateT (Option (Name × Float)) M Unit := do
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
    if let some (bestLabel, bestScore) := bestMatch? then
      addUnresolvedCompletionItem bestLabel (.const declName) (← getCompletionKindForDecl c) bestScore
  -- Recall that aliases may not be atomic and include the namespace where they were created.
  let matchAlias (ns : Name) (alias : Name) : Option Float :=
    if ns.isPrefixOf alias then
      matchAtomic id (alias.replacePrefix ns Name.anonymous)
    else
      none
  let eligibleHeaderDecls ← getEligibleHeaderDecls env
  -- Auxiliary function for `alias`
  let addAlias (alias : Name) (declNames : List Name) (score : Float) : M Unit := do
    declNames.forM fun declName => do
      if allowCompletion eligibleHeaderDecls env declName then
        addUnresolvedCompletionItemForDecl (.mkSimple alias.getString!) declName score
  -- search explicitly open `ids`
  for openDecl in ctx.openDecls do
    match openDecl with
    | OpenDecl.explicit openedId resolvedId =>
      if allowCompletion eligibleHeaderDecls env resolvedId then
        if let some score := matchAtomic id openedId then
          addUnresolvedCompletionItemForDecl (.mkSimple openedId.getString!) resolvedId score
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
      if let some score := fuzzyMatchScoreWithThreshold? s keyword then
        addKeywordCompletionItem keyword score
  -- Search namespaces
  completeNamespaces ctx id danglingDot

private def idCompletion
    (params        : CompletionParams)
    (ctx           : ContextInfo)
    (lctx          : LocalContext)
    (stx           : Syntax)
    (id            : Name)
    (hoverInfo     : HoverInfo)
    (danglingDot   : Bool)
    : IO (Option CompletionList) :=
  runM params ctx lctx do
    idCompletionCore ctx stx id hoverInfo danglingDot

private def unfoldeDefinitionGuarded? (e : Expr) : MetaM (Option Expr) :=
  try unfoldDefinition? e catch _ => pure none

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
partial def cmpModPrivate (n₁ n₂ : Name) : Ordering :=
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
def NameSetModPrivate := RBTree Name cmpModPrivate

/--
  Given a type, try to extract relevant type names for dot notation field completion.
  We extract the type name, parent struct names, and unfold the type.
  The process mimics the dot notation elaboration procedure at `App.lean` -/
private partial def getDotCompletionTypeNames (type : Expr) : MetaM NameSetModPrivate :=
  return (← visit type |>.run RBTree.empty).2
where
  visit (type : Expr) : StateRefT NameSetModPrivate MetaM Unit := do
    let .const typeName _ := type.getAppFn | return ()
    modify fun s => s.insert typeName
    if isStructure (← getEnv) typeName then
      for parentName in (← getAllParentStructures typeName) do
        modify fun s => s.insert parentName
    let some type ← unfoldeDefinitionGuarded? type | return ()
    visit type

private def dotCompletion
    (params        : CompletionParams)
    (ctx           : ContextInfo)
    (info          : TermInfo)
    (hoverInfo     : HoverInfo)
    : IO (Option CompletionList) :=
  runM params ctx info.lctx do
    let nameSet ← try
      getDotCompletionTypeNames (← instantiateMVars (← inferType info.expr))
    catch _ =>
      pure RBTree.empty

    if nameSet.isEmpty then
      let stx := info.stx
      if stx.isIdent then
        idCompletionCore ctx stx stx.getId hoverInfo (danglingDot := false)
      else if stx.getKind == ``Lean.Parser.Term.completion && stx[0].isIdent then
        -- TODO: truncation when there is a dangling dot
        idCompletionCore ctx stx stx[0].getId HoverInfo.after (danglingDot := true)
      else
        failure
      return

    forEligibleDeclsM fun declName c => do
      let unnormedTypeName := declName.getPrefix
      if ! nameSet.contains unnormedTypeName then
        return
      let some declName ← normPrivateName? declName
        | return
      let typeName := declName.getPrefix
      if ! (← isDotCompletionMethod typeName c) then
        return
      let completionKind ← getCompletionKindForDecl c
      addUnresolvedCompletionItem (.mkSimple c.name.getString!) (.const c.name) (kind := completionKind) 1

private def dotIdCompletion
    (params        : CompletionParams)
    (ctx           : ContextInfo)
    (lctx          : LocalContext)
    (id            : Name)
    (expectedType? : Option Expr)
    : IO (Option CompletionList) :=
  runM params ctx lctx do
    let some expectedType := expectedType?
      | return ()

    let resultTypeFn := (← instantiateMVars expectedType).cleanupAnnotations.getAppFn.cleanupAnnotations
    let .const .. := resultTypeFn
      | return ()

    let nameSet ← try
      getDotCompletionTypeNames resultTypeFn
    catch _ =>
      pure RBTree.empty

    forEligibleDeclsM fun declName c => do
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
        addUnresolvedCompletionItem (.mkSimple c.name.getString!) (.const c.name) completionKind 1
        return

      let some (label, score) ← matchDecl? typeName id (danglingDot := false) declName | pure ()
      addUnresolvedCompletionItem label (.const c.name) completionKind score

private def fieldIdCompletion
    (params     : CompletionParams)
    (ctx        : ContextInfo)
    (lctx       : LocalContext)
    (id         : Name)
    (structName : Name)
    : IO (Option CompletionList) :=
  runM params ctx lctx do
    let idStr := id.toString
    let fieldNames := getStructureFieldsFlattened (← getEnv) structName (includeSubobjectFields := false)
    for fieldName in fieldNames do
      let .str _ fieldName := fieldName | continue
      let some score := fuzzyMatchScoreWithThreshold? idStr fieldName | continue
      let item := { label := fieldName, detail? := "field", documentation? := none, kind? := CompletionItemKind.field }
      addItem item score

private def optionCompletion
    (params : CompletionParams)
    (ctx    : ContextInfo)
    (stx    : Syntax)
    (caps   : ClientCapabilities)
    : IO (Option CompletionList) :=
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
             textEdit? := textEdit
             data? := toJson { params, id? := none : CompletionItemDataWithId } }, score)
    return some { items := sortCompletionItems items, isIncomplete := true }

private def tacticCompletion (params : CompletionParams) (ctx : ContextInfo)
    : IO (Option CompletionList) := ctx.runMetaM .empty do
  let allTacticDocs ← Tactic.Doc.allTacticDocs
  let items : Array (CompletionItem × Float) := allTacticDocs.map fun tacticDoc =>
    ({
      label          := tacticDoc.userName
      detail?        := none
      documentation? := tacticDoc.docString.map fun docString =>
        { value := docString, kind := MarkupKind.markdown : MarkupContent }
      kind?          := CompletionItemKind.keyword
      data?          := toJson { params, id? := none : CompletionItemDataWithId }
    }, 1)
  return some { items := sortCompletionItems items, isIncomplete := true }

private def findBest?
    (infoTree : InfoTree)
    (gt : α → α → Bool)
    (f : ContextInfo → Info → PersistentArray InfoTree → Option α)
    : Option α :=
  infoTree.visitM (m := Id) (postNode := choose) |>.join
where
  choose
      (ctx : ContextInfo)
      (info : Info)
      (cs : PersistentArray InfoTree)
      (childValues : List (Option (Option α)))
      : Option α :=
    let bestChildValue := childValues.map (·.join) |>.foldl (init := none) fun v best =>
      if isBetter v best then
        v
      else
        best
    if let some v := f ctx info cs then
      if isBetter v bestChildValue then
        v
      else
        bestChildValue
    else
      bestChildValue
  isBetter (a b : Option α) : Bool :=
    match a, b with
    | none,   none   => false
    | some _, none   => true
    | none,   some _ => false
    | some a, some b => gt a b

/--
If there are `Info`s that contain `hoverPos` and have a nonempty `LocalContext`,
yields the closest one of those `Info`s.
Otherwise, yields the closest `Info` that contains `hoverPos` and has an empty `LocalContext`.
-/
private def findClosestInfoWithLocalContextAt?
    (hoverPos : String.Pos)
    (infoTree : InfoTree)
    : Option (ContextInfo × Info) :=
  findBest? infoTree isBetter fun ctx info _ =>
    if info.occursInOrOnBoundary hoverPos then
      (ctx, info)
    else
      none
where
  isBetter (a b : ContextInfo × Info) : Bool :=
    let (_, ia) := a
    let (_, ib) := b
    if !ia.lctx.isEmpty && ib.lctx.isEmpty then
      true
    else if ia.lctx.isEmpty && !ib.lctx.isEmpty then
      false
    else if ia.isSmaller ib then
      true
    else if ib.isSmaller ia then
      false
    else
      false

private def findSyntheticIdentifierCompletion?
    (hoverPos : String.Pos)
    (infoTree : InfoTree)
    : Option (HoverInfo × ContextInfo × CompletionInfo) := do
  let some (ctx, info) := findClosestInfoWithLocalContextAt? hoverPos infoTree
    | none
  let some stack := info.stx.findStack? (·.getRange?.any (·.contains hoverPos (includeStop := true)))
    | none
  let stack := stack.dropWhile fun (stx, _) => !(stx matches `($_:ident) || stx matches `($_:ident.))
  let some (stx, _) := stack.head?
    | none
  let isDotIdCompletion := stack.any fun (stx, _) => stx matches `(.$_:ident)
  if isDotIdCompletion then
    -- An identifier completion is never useful in a dotId completion context.
    none
  let some (id, danglingDot) :=
      match stx with
      | `($id:ident) => some (id.getId, false)
      | `($id:ident.) => some (id.getId, true)
      | _ => none
    | none
  let tailPos := stx.getTailPos?.get!
  let hoverInfo :=
    if hoverPos < tailPos then
      HoverInfo.inside (tailPos - hoverPos).byteIdx
    else
      HoverInfo.after
  some (hoverInfo, ctx, .id stx id danglingDot info.lctx none)

private partial def getIndentationAmount (fileMap : FileMap) (line : Nat) : Nat := Id.run do
  let lineStartPos := fileMap.lineStart line
  let lineEndPos := fileMap.lineStart (line + 1)
  let mut it : String.Iterator := ⟨fileMap.source, lineStartPos⟩
  let mut indentationAmount := 0
  while it.pos < lineEndPos do
    let c := it.curr
    if c = ' ' || c = '\t' then
      indentationAmount := indentationAmount + 1
    else
      break
    it := it.next
  return indentationAmount

private partial def isSyntheticTacticCompletion
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    : Bool := Id.run do
  let hoverFilePos := fileMap.toPosition hoverPos
  let mut hoverLineIndentation := getIndentationAmount fileMap hoverFilePos.line
  if hoverFilePos.column < hoverLineIndentation then
    -- Ignore trailing whitespace after the cursor
    hoverLineIndentation := hoverFilePos.column
  go hoverFilePos hoverLineIndentation cmdStx 0
where
  go
      (hoverFilePos : Position)
      (hoverLineIndentation : Nat)
      (stx : Syntax)
      (leadingWs : Nat)
      : Bool := Id.run do
    match stx.getPos?, stx.getTailPos? with
    | some startPos, some endPos =>
      let isCursorInCompletionRange :=
        startPos.byteIdx - leadingWs <= hoverPos.byteIdx
          && hoverPos.byteIdx <= endPos.byteIdx + stx.getTrailingSize
      if ! isCursorInCompletionRange then
        return false
      let mut wsBeforeArg := leadingWs
      for arg in stx.getArgs do
        if go hoverFilePos hoverLineIndentation arg wsBeforeArg then
          return true
        -- We must account for the whitespace before an argument because the syntax nodes we use
        -- to identify tactic blocks only start *after* the whitespace following a `by`, and we
        -- want to provide tactic completions in that whitespace as well.
        -- This method of computing whitespace assumes that there are no syntax nodes without tokens
        -- after `by` and before the first proper tactic syntax.
        wsBeforeArg := arg.getTrailingSize
      return isCompletionInEmptyTacticBlock stx
        || isCompletionAfterSemicolon stx
        || isCompletionOnTacticBlockIndentation hoverFilePos hoverLineIndentation stx
    | _, _ =>
      -- Empty tactic blocks typically lack ranges since they do not contain any tokens.
      -- We do not perform more precise range checking in this case because we assume that empty
      -- tactic blocks always occur within other syntax with ranges that let us narrow down the
      -- search to the degree that we can be sure that the cursor is indeed in this empty tactic
      -- block.
      return isCompletionInEmptyTacticBlock stx

  isCompletionOnTacticBlockIndentation
      (hoverFilePos : Position)
      (hoverLineIndentation : Nat)
      (stx : Syntax)
      : Bool := Id.run do
    let isCursorInIndentation := hoverFilePos.column <= hoverLineIndentation
    if ! isCursorInIndentation then
      -- Do not trigger tactic completion at the end of a properly indented tactic block line since
      -- that line might already have entered term mode by that point.
      return false
    let some tacticsNode := getTacticsNode? stx
      | return false
    let some firstTacticPos := tacticsNode.getPos?
      | return false
    let firstTacticLine := fileMap.toPosition firstTacticPos |>.line
    let firstTacticIndentation := getIndentationAmount fileMap firstTacticLine
    -- This ensures that we do not accidentally provide tactic completions in a term mode proof -
    -- tactic completions are only provided at the same indentation level as the other tactics in
    -- that tactic block.
    let isCursorInTacticBlock := hoverLineIndentation == firstTacticIndentation
    return isCursorInProperWhitespace && isCursorInTacticBlock

  isCompletionAfterSemicolon (stx : Syntax) : Bool := Id.run do
    let some tacticsNode := getTacticsNode? stx
      | return false
    let tactics := tacticsNode.getArgs
    -- We want to provide completions in the case of `skip;<CURSOR>`, so the cursor must only be on
    -- whitespace, not in proper whitespace.
    return isCursorOnWhitspace && tactics.any fun tactic => Id.run do
      let some tailPos := tactic.getTailPos?
        | return false
      let isCursorAfterSemicolon :=
        tactic.isToken ";"
          && tailPos.byteIdx <= hoverPos.byteIdx
          && hoverPos.byteIdx <= tailPos.byteIdx + tactic.getTrailingSize
      return isCursorAfterSemicolon

  getTacticsNode? (stx : Syntax) : Option Syntax :=
    if stx.getKind == `Lean.Parser.Tactic.tacticSeq1Indented then
      some stx[0]
    else if stx.getKind == `Lean.Parser.Tactic.tacticSeqBracketed then
      some stx[1]
    else
      none

  isCompletionInEmptyTacticBlock (stx : Syntax) : Bool :=
    isCursorInProperWhitespace && isEmptyTacticBlock stx

  isCursorOnWhitspace : Bool :=
    fileMap.source.atEnd hoverPos || (fileMap.source.get hoverPos).isWhitespace

  isCursorInProperWhitespace : Bool :=
    (fileMap.source.atEnd hoverPos || (fileMap.source.get hoverPos).isWhitespace)
      && (fileMap.source.get (hoverPos - ⟨1⟩)).isWhitespace

  isEmptyTacticBlock (stx : Syntax) : Bool :=
    stx.getKind == `Lean.Parser.Tactic.tacticSeq && isEmpty stx
      || stx.getKind == `Lean.Parser.Tactic.tacticSeq1Indented && isEmpty stx
      || stx.getKind == `Lean.Parser.Tactic.tacticSeqBracketed && isEmpty stx[1]

  isEmpty : Syntax → Bool
    | .missing       => true
    | .ident ..      => false
    | .atom ..       => false
    | .node _ _ args => args.all isEmpty

private partial def findOutermostContextInfo? (i : InfoTree) : Option ContextInfo :=
  go i
where
  go (i : InfoTree) : Option ContextInfo := do
    match i with
  | .context ctx i =>
    match ctx with
    | .commandCtx ctxInfo =>
      some { ctxInfo with }
    | _ =>
      -- This shouldn't happen (see the `PartialContextInfo` docstring),
      -- but let's continue searching regardless
      go i
  | .node _ cs =>
    cs.findSome? go
  | .hole .. =>
    none

private def findSyntheticTacticCompletion?
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    : Option (HoverInfo × ContextInfo × CompletionInfo) := do
  let ctx ← findOutermostContextInfo? infoTree
  if ! isSyntheticTacticCompletion fileMap hoverPos cmdStx then
    none
  -- Neither `HoverInfo` nor the syntax in `.tactic` are important for tactic completion.
  return (HoverInfo.after, ctx, .tactic .missing)

private def findCompletionInfoAt?
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    : Option (HoverInfo × ContextInfo × CompletionInfo) :=
  let ⟨hoverLine, _⟩ := fileMap.toPosition hoverPos
  match infoTree.foldInfo (init := none) (choose hoverLine) with
  | some (hoverInfo, ctx, Info.ofCompletionInfo info) =>
    some (hoverInfo, ctx, info)
  | _ =>
    findSyntheticTacticCompletion? fileMap hoverPos cmdStx infoTree <|>
      findSyntheticIdentifierCompletion? hoverPos infoTree
where
  choose
      (hoverLine : Nat)
      (ctx       : ContextInfo)
      (info      : Info)
      (best?     : Option (HoverInfo × ContextInfo × Info))
      : Option (HoverInfo × ContextInfo × Info) :=
    if !info.isCompletion then
      best?
    else if info.occursInOrOnBoundary hoverPos then
      let headPos := info.pos?.get!
      let tailPos := info.tailPos?.get!
      let hoverInfo :=
        if hoverPos < tailPos then
          HoverInfo.inside (hoverPos - headPos).byteIdx
        else
          HoverInfo.after
      let ⟨headPosLine, _⟩ := fileMap.toPosition headPos
      let ⟨tailPosLine, _⟩ := fileMap.toPosition info.tailPos?.get!
      if headPosLine != hoverLine || headPosLine != tailPosLine then
        best?
      else match best? with
        | none              => (hoverInfo, ctx, info)
        | some (_, _, best) =>
          if isBetter info best then
            (hoverInfo, ctx, info)
          else
            best?
    else
      best?

  isBetter : Info → Info → Bool
    | i₁@(.ofCompletionInfo ci₁), i₂@(.ofCompletionInfo ci₂) =>
      -- Use the smallest info available and prefer non-id completion over id completions as a
      -- tie-breaker.
      -- This is necessary because the elaborator sometimes generates both for the same range.
      -- If two infos are equivalent, always prefer the first one.
      if i₁.isSmaller i₂ then
        true
      else if i₂.isSmaller i₁ then
        false
      else if !(ci₁ matches .id ..) && ci₂ matches .id .. then
        true
      else if ci₁ matches .id .. && !(ci₂ matches .id ..) then
        false
      else
        true
    | .ofCompletionInfo _, _ => true
    | _, .ofCompletionInfo _ => false
    | _, _ => true

/--
Assigns the `CompletionItem.sortText?` for all items in `completions` according to their order
in `completions`. This is necessary because clients will use their own sort order if the server
does not set it.
-/
private def assignSortTexts (completions : CompletionList) : CompletionList := Id.run do
  if completions.items.isEmpty then
    return completions
  let items := completions.items.mapIdx fun i item =>
    { item with sortText? := toString i }
  let maxDigits := items[items.size - 1]!.sortText?.get!.length
  let items := items.map fun item =>
    let sortText := item.sortText?.get!
    let pad := List.replicate (maxDigits - sortText.length) '0' |>.asString
    { item with sortText? := pad ++ sortText }
  { completions with items := items }

partial def find?
    (params   : CompletionParams)
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    (caps     : ClientCapabilities)
    : IO (Option CompletionList) := do
  let some (hoverInfo, ctx, info) := findCompletionInfoAt? fileMap hoverPos cmdStx infoTree
    | return none
  let completionList? ←
    match info with
    | .dot info .. =>
      dotCompletion params ctx info hoverInfo
    | .id stx id danglingDot lctx .. =>
      idCompletion params ctx lctx stx id hoverInfo danglingDot
    | .dotId _ id lctx expectedType? =>
      dotIdCompletion params ctx lctx id expectedType?
    | .fieldId _ id lctx structName =>
      fieldIdCompletion params ctx lctx id structName
    | .option stx =>
      optionCompletion params ctx stx caps
    | .tactic .. =>
      tacticCompletion params ctx
    | _ => return none
  return completionList?.map assignSortTexts

/--
Fills the `CompletionItem.detail?` field of `item` using the pretty-printed type identified by `id`
in the context found at `hoverPos` in `infoTree`.
-/
def resolveCompletionItem?
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    (item     : CompletionItem)
    (id       : CompletionIdentifier)
    : IO CompletionItem := do
  let some (_, ctx, info) := findCompletionInfoAt? fileMap hoverPos cmdStx infoTree
    | return item
  ctx.runMetaM info.lctx (item.resolve id)

end Lean.Server.Completion
