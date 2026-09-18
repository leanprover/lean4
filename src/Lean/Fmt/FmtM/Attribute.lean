/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.KeyedDeclsAttribute
public import Lean.Util.ShareCommon
public import Lean.Fmt.FmtM.LineInfo
import Lean.Compiler.InitAttr
import Lean.ExtraModUses
import Lean.Fmt.Util.Module
public import Lean.Fmt.Core.Formatter
public import Lean.Elab.InfoTree.Types
import Lean.Elab.InfoTree.Basic

namespace Lean.Fmt

/--
Cost type used for the documents produced by `FmtM` formatters: the default cost function with a
page width limit of 100 and an optimality cutoff width of 200.
-/
public abbrev FmtCost := DefaultCost 100 200

public structure FormattedWhitespace where
  formattedLeadingRanges : Array Syntax.Range
  formattedTrailingRanges : Array Syntax.Range
deriving Repr

public structure MissingFormatter where
  kind : SyntaxNodeKind

public structure PartialFormatter where
  stx : Syntax
  formatterName : Name

public structure Context where
  env : Environment
  text : FileMap
  /--
  Resolves the `choice` node at the given range to the alternative that the elaborator picked.

  `fmtChoiceNode` calls this only when the alternatives do not all render to the same document, so
  an implementation may block on the elaboration that produces the resolution.
  A `none` result raises `Error.ambiguousChoiceNode`.
  -/
  resolveChoiceNode : Syntax.Range → Option Elab.ChoiceResolutionInfo
  opts : Options
  lineInfos : Array SyntaxLineInfo

/-- Looks up the resolution of the `choice` node at `range` in `infoTree`. -/
public def findChoiceResolution? (infoTree : Elab.InfoTree) (range : Syntax.Range)
    : Option Elab.ChoiceResolutionInfo := do
  let .ofChoiceResolutionInfo i ←
      infoTree.findInfo? fun
        | .ofChoiceResolutionInfo i => i.stx.getRange? == range
        | _ => false
    | none
  return i

public inductive RangeKind where
  | whitespace
  | node
  | text
deriving Inhabited

public structure BacktrackableState where
  tags : Std.HashMap Syntax.Range (Array TagId × RangeKind)
deriving Inhabited

public structure State extends BacktrackableState where
  shareCommonState : ShareCommon.State ShareCommon.objectFactory
  freshTagId : TagId
  missingFormatters : Std.HashMap Syntax.Range MissingFormatter
  partialFormatters : Std.HashMap Syntax.Range PartialFormatter
deriving Inhabited

public instance : EStateM.Backtrackable BacktrackableState State where
  save s := s.toBacktrackableState
  restore s d := { s with toBacktrackableState := d }

public structure TaggedDoc.MetaData where
  v : Dynamic
  propagate : Dynamic → (Doc FmtCost → Doc FmtCost) → Dynamic

public structure TaggedDoc where
  doc : Doc FmtCost
  metaData : List TaggedDoc.MetaData := []
deriving Inhabited

end Lean.Fmt

namespace Lean

public abbrev FmtM α := ReaderT Fmt.Context (EStateM Fmt.Error Fmt.State) α
public abbrev Fmt := Syntax → FmtM Fmt.TaggedDoc

end Lean

namespace Lean.Fmt

/--
Determines the formatter to use for a syntax node kind, together with the name of the declaration
it originates from (which is reported when the formatter turns out to be incomplete).
Yields `none` if the provider is not responsible for the kind.
-/
public abbrev FmtProvider := Environment → Options → SyntaxNodeKind → Option (Name × Fmt)

public structure FmtProviderEntry where
  priority : Nat
  provider : FmtProvider

/-- Inserts `entry` after all entries of greater or equal priority. -/
private def insertFmtProvider (providers : Array FmtProviderEntry) (entry : FmtProviderEntry)
    : Array FmtProviderEntry :=
  let i := providers.findIdx? (·.priority < entry.priority) |>.getD providers.size
  providers.insertIdx! i entry

/-- The list of builtin `FmtProvider`s, ordered by decreasing priority. -/
builtin_initialize builtinFmtProvidersRef : IO.Ref (Array FmtProviderEntry) ← IO.mkRef #[]

/--
Adds a new builtin `FmtProvider`. Providers are consulted in order of decreasing priority and the
first provider that is responsible for a syntax node kind determines its formatter. Providers of
equal priority are consulted in the order in which they were added, with the builtin ones coming
before those registered with `@[fmt_provider]`. The priorities used by core are:
* 1100 for choice nodes,
* 1000 for the formatters registered with `@[{builtin_}fmt]`,
* 900 for antiquotations,
* 800 for the formatters registered with a specialized attribute
  (`@[{builtin_}infix_fmt]`, `@[{builtin_}conditional_fmt]`, `@[{builtin_}quantifier_fmt]`),
* 600 for the operator formatters derived from the `ParserDescr` of a notation,
* 400 for the atomic formatter derived from the `ParserDescr` of syntax that only parses atoms.

This function should only be used from within the `Lean` package; downstream code registers
`FmtProvider`s with the `@[fmt_provider]` attribute instead.
-/
public def addBuiltinFmtProvider (priority : Nat) (provider : FmtProvider) : IO Unit :=
  builtinFmtProvidersRef.modify (insertFmtProvider · { priority, provider })

/-- Interpret a `FmtProvider` from the environment. -/
def mkFmtProvider (constName : Name) : ImportM FmtProvider := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck FmtProvider opts ``FmtProvider constName

/--
An extension which keeps track of the builtin `FmtProvider`s together with those registered with
`@[fmt_provider]`, ordered by decreasing priority.
-/
builtin_initialize fmtProvidersExt
    : PersistentEnvExtension (Name × Nat) (Name × FmtProviderEntry)
      (Array (Name × Nat) × Array FmtProviderEntry) ←
  registerPersistentEnvExtension {
    mkInitial := return (#[], ← builtinFmtProvidersRef.get)
    addImportedFn := fun as => do
      (#[], ·) <$> as.foldlM (init := ← builtinFmtProvidersRef.get) fun s as =>
        as.foldlM (init := s) fun s (declName, priority) =>
          return insertFmtProvider s { priority, provider := ← mkFmtProvider declName }
    addEntryFn := fun (names, providers) (declName, entry) =>
      (names.push (declName, entry.priority), insertFmtProvider providers entry)
    exportEntriesFn := (·.1)
  }

/-- The registered `FmtProvider`s, ordered by decreasing priority. -/
public def getFmtProviders (env : Environment) : Array FmtProviderEntry :=
  fmtProvidersExt.getState env |>.2

/--
Adds the `@[fmt_provider]` attribute, which is applied to declarations of type
`Lean.Fmt.FmtProvider` to make them determine the formatters of the syntax node kinds they are
responsible for. Its optional argument is the provider's priority, which defaults to `1000`; see
`addBuiltinFmtProvider` for the priorities used by core.
-/
builtin_initialize
  registerBuiltinAttribute {
    name := `fmt_provider
    descr :=
      "Registers a function of type `Lean.Fmt.FmtProvider` that determines the \
        formatters of the syntax node kinds it is responsible for."
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      let priority ← Attribute.Builtin.getPrio stx
      ensureAttrDeclIsMeta `fmt_provider decl kind
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal `fmt_provider kind
      let declType := (← getConstInfo decl).type
      unless declType.isConstOf ``FmtProvider do
        throwAttrDeclNotOfExpectedType `fmt_provider decl declType (mkConst ``FmtProvider)
      let entry := { priority, provider := ← mkFmtProvider decl }
      setEnv <| fmtProvidersExt.addEntry (← getEnv) (decl, entry)
  }

/-- Whether the comment was placed in leading or trailing whitespace in the input `Syntax`. -/
public inductive Comment.Whitespace where
  | leading
  | trailing
deriving Inhabited, BEq, Repr

/-- Comment placement in the input `Syntax`. -/
public inductive Comment.Placement where
  | afterToken
  | onLineBeforeToken
deriving Inhabited, BEq, Repr

/-- Kind of comment in the input `Syntax`. -/
public inductive Comment.Kind where
  | lineComment
  | blockComment
deriving Inhabited, BEq, Repr

/-- Comment extracted from an input `Syntax`. -/
public structure Comment where
  /-- Kind of comment in the input `Syntax`. -/
  kind : Comment.Kind
  /-- Comment placement in the input `Syntax`. -/
  placement : Comment.Placement
  /-- Range of the original token in the input `Syntax` that this comment was attached to. -/
  originalTokenRange : Syntax.Range
  /-- Range of the trailing whitespace in the input `Syntax`. -/
  originalWhitespaceRange : Syntax.Range
  /-- Whether the comment was placed in leading or trailing whitespace in the input `Syntax`. -/
  originalWhitespaceKind : Comment.Whitespace
  /--
  Content of the comment separated into lines.
  Excludes the comment separators and all whitespace within the comment that serves as indentation
  of the comment relative to the least indented line with content in the comment.
  -/
  content : Array String
deriving Inhabited, BEq, Repr

/-- Input that a `CommentCollector` is consulted with. -/
public structure CommentCollector.Context where
  env : Environment
  opts : Options
  /-- Line information for the input `Syntax`. -/
  lineInfos : Array SyntaxLineInfo

/--
Associates the comments of a syntax node with the syntax ranges that they should be attached to,
overriding the association that `collectComments` determines on its own.
A collector is consulted for every `Syntax.node` in the input `Syntax` and must leave out the
comments it is not responsible for, so that they can be associated by a collector of lower priority
or, failing that, by `collectComments` itself.
-/
public abbrev CommentCollector := CommentCollector.Context → Syntax → Array (Comment × Syntax.Range)

public structure CommentCollectorEntry where
  priority : Nat
  collector : CommentCollector

/-- Inserts `entry` after all entries of greater or equal priority. -/
private def insertCommentCollector
    (collectors : Array CommentCollectorEntry) (entry : CommentCollectorEntry)
    : Array CommentCollectorEntry :=
  let i := collectors.findIdx? (·.priority < entry.priority) |>.getD collectors.size
  collectors.insertIdx! i entry

/-- The list of builtin `CommentCollector`s, ordered by decreasing priority. -/
builtin_initialize builtinCommentCollectorsRef : IO.Ref (Array CommentCollectorEntry) ← IO.mkRef #[]

/--
Adds a new builtin `CommentCollector`. Collectors are consulted for every syntax node in order of
decreasing priority; when two collectors claim the same comment, the one of greater priority wins.
Collectors of equal priority are consulted in the order in which they were added, with the builtin
ones coming before those registered with `@[comment_collector]`. The priorities used by core are:
* 500 for `infixOperatorCommentCollector`.

This function should only be used from within the `Lean` package; downstream code registers
`CommentCollector`s with the `@[comment_collector]` attribute instead.
-/
public def addBuiltinCommentCollector (priority : Nat) (collector : CommentCollector) : IO Unit :=
  builtinCommentCollectorsRef.modify (insertCommentCollector · { priority, collector })

/-- Interpret a `CommentCollector` from the environment. -/
def mkCommentCollector (constName : Name) : ImportM CommentCollector := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck CommentCollector opts ``CommentCollector constName

/--
An extension which keeps track of the builtin `CommentCollector`s together with those registered
with `@[comment_collector]`, ordered by decreasing priority.
-/
builtin_initialize commentCollectorsExt
    : PersistentEnvExtension (Name × Nat) (Name × CommentCollectorEntry)
      (Array (Name × Nat) × Array CommentCollectorEntry) ←
  registerPersistentEnvExtension {
    mkInitial := return (#[], ← builtinCommentCollectorsRef.get)
    addImportedFn := fun as => do
      (#[], ·) <$> as.foldlM (init := ← builtinCommentCollectorsRef.get) fun s as =>
        as.foldlM (init := s) fun s (declName, priority) =>
          return insertCommentCollector s { priority, collector := ← mkCommentCollector declName }
    addEntryFn := fun (names, collectors) (declName, entry) =>
      (names.push (declName, entry.priority), insertCommentCollector collectors entry)
    exportEntriesFn := (·.1)
  }

/-- The registered `CommentCollector`s, ordered by decreasing priority. -/
public def getCommentCollectors (env : Environment) : Array CommentCollectorEntry :=
  commentCollectorsExt.getState env |>.2

/--
Adds the `@[comment_collector]` attribute, which is applied to declarations of type
`Lean.Fmt.CommentCollector` to make them determine the syntax ranges that the comments of the
syntax nodes they are responsible for are associated with. Its optional argument is the collector's
priority, which defaults to `1000`; see `addBuiltinCommentCollector`.
-/
builtin_initialize
  registerBuiltinAttribute {
    name := `comment_collector
    descr :=
      "Registers a function of type `Lean.Fmt.CommentCollector` that determines the \
        syntax ranges that the comments of the syntax nodes it is responsible for are associated \
        with."
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      let priority ← Attribute.Builtin.getPrio stx
      ensureAttrDeclIsMeta `comment_collector decl kind
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal `comment_collector kind
      let declType := (← getConstInfo decl).type
      unless declType.isConstOf ``CommentCollector do
        throwAttrDeclNotOfExpectedType `comment_collector decl declType (mkConst ``CommentCollector)
      let entry := { priority, collector := ← mkCommentCollector decl }
      setEnv <| commentCollectorsExt.addEntry (← getEnv) (decl, entry)
  }

/--
The `FmtProvider` of an attribute that registers formatters keyed by syntax node kind, where `mk`
turns a registered value into the formatter it stands for.
-/
public def keyedFmtProvider {α : Type} (attr : KeyedDeclsAttribute α) (mk : α → Fmt)
    : FmtProvider := fun env _ kind => do
  let entry ← attr.getEntries env kind |>.head?
  return (entry.declName, mk entry.value)

/-- Elaborates the syntax node kind argument of an attribute that registers a formatter. -/
private def evalFmtAttributeKey
    (attrName : Name) (extraKinds : List SyntaxNodeKind := []) (builtin : Bool) (stx : Syntax)
    : AttrM Name := do
  let env ← getEnv
  let stx ← Attribute.Builtin.getIdent stx
  let id := stx.getId
  -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
  -- synthesize a formatter for it immediately, so we just check for a declaration in this case
  if !(builtin && (env.find? id).isSome || Parser.isValidSyntaxNodeKind env id
    || extraKinds.contains id)
  then
    throwError "Invalid `[{attrName}]` argument: Unknown syntax kind `{id}`"
  if (← getEnv).contains id then
    recordExtraModUseFromDecl (isMeta := false) id
    if (← Elab.getInfoState).enabled then
      Elab.addConstInfo stx id none
  pure id

public unsafe builtin_initialize fmtAttribute : KeyedDeclsAttribute Fmt ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_fmt
    name := `fmt
    descr := "Register an Fmt formatter for a syntax node kind."
    valueTypeName := `Lean.Fmt
    evalKey := evalFmtAttributeKey `fmt [moduleKind, cmdsKind, headerKind]
  }

/--
Determines whether the given term, when it occurs as an argument of an application,
propagates the stickiness of its right-hand side to the full application.
-/
public abbrev StickyTermFn := TSyntax `term → Bool

/-- Interpret a `StickyTermFn` from the environment. -/
def mkStickyTermFn (constName : Name) : ImportM StickyTermFn := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck StickyTermFn opts ``StickyTermFn constName

/-- The list of builtin `StickyTermFn`s. -/
builtin_initialize builtinStickyTermFnsRef : IO.Ref (Array StickyTermFn) ← IO.mkRef #[]

/--
Adds a new builtin `StickyTermFn`.
This function should only be used from within the `Lean` package.
-/
public def addBuiltinStickyTermFn (f : StickyTermFn) : IO Unit :=
  builtinStickyTermFnsRef.modify (·.push f)

/-- An extension which keeps track of registered `StickyTermFn`s. -/
builtin_initialize stickyTermFnsExt
    : PersistentEnvExtension Name (Name × StickyTermFn) (Array Name × Array StickyTermFn) ←
  registerPersistentEnvExtension {
    mkInitial := return (#[], ← builtinStickyTermFnsRef.get)
    addImportedFn := fun as => do
      (#[], ·) <$> as.foldlM (init := ← builtinStickyTermFnsRef.get) fun s as =>
        as.foldlM (init := s) fun s n => s.push <$> mkStickyTermFn n
    addEntryFn := fun (names, fns) (n, f) => (names.push n, fns.push f)
    exportEntriesFn := (·.1)
  }

/--
Adds the `@[{builtin_}fmt_sticky_term]` attribute, which is applied to declarations of type
`StickyTermFn` for use in the formatting of applications.
-/
builtin_initialize
  let mkAttr (builtin : Bool) (name : Name) :=
    registerBuiltinAttribute {
      name
      descr :=
        (if builtin then "(builtin) " else "")
          ++ "Marks a function of type `Lean.Fmt.StickyTermFn` that determines whether a term \
            propagates the stickiness of its right-hand side in applications."
      applicationTime := .afterCompilation
      add := fun decl stx kind => do
        Attribute.Builtin.ensureNoArgs stx
        if !builtin then
          ensureAttrDeclIsMeta name decl kind
        unless kind == AttributeKind.global do
          throwAttrMustBeGlobal name kind
        let declType := (← getConstInfo decl).type
        unless declType.isConstOf ``StickyTermFn do
          throwAttrDeclNotOfExpectedType name decl declType (mkConst ``StickyTermFn)
        if builtin then
          declareBuiltin decl <| mkApp (mkConst ``addBuiltinStickyTermFn) (mkConst decl)
        else
          setEnv <| stickyTermFnsExt.addEntry (← getEnv) (decl, ← mkStickyTermFn decl)
    }
  mkAttr true `builtin_fmt_sticky_term
  mkAttr false `fmt_sticky_term

/--
Returns `true` if any function registered with the `@[{builtin_}fmt_sticky_term]` attribute
determines that `t` propagates the stickiness of its right-hand side.
-/
public def propagatesRhsStickiness (env : Environment) (t : TSyntax `term) : Bool :=
  (stickyTermFnsExt.getState env).2.any (· t)

public inductive InfixOperationAssociativity where
  | left
  | right
  | middle
deriving Inhabited, BEq

public structure InfixOperationPrecs where
  prec : Nat
  lhsPrec : Nat
  rhsPrec : Nat
deriving Inhabited, BEq

/-- The infix operation that a syntax node kind denotes. -/
public structure InfixOperation where
  sparse : Bool
  separateFinalOperand : Bool := false
  precs? : Option InfixOperationPrecs := none
  /--
  Further syntax node kinds that an operator chain containing this operator may continue with.
  -/
  extendedChainKinds : Std.HashSet SyntaxNodeKind := {}
deriving Inhabited, BEq

public unsafe builtin_initialize infixFmtAttribute : KeyedDeclsAttribute InfixOperation ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_infix_fmt
    name := `infix_fmt
    descr := "Register an Fmt infix operation formatter for a syntax node kind."
    valueTypeName := `Lean.Fmt.InfixOperation
    evalKey := evalFmtAttributeKey `infix_fmt
  }

public structure Conditional.ElseIf where
  elseTk : Syntax
  ifTk : Syntax
  cond : TaggedDoc
  thenTk : Syntax
  body : Syntax

public structure Conditional where
  ifTk : Syntax
  cond : TaggedDoc
  thenTk : Syntax
  thenBody : Syntax
  elseIfs : Array Conditional.ElseIf := #[]
  elseTk? : Option Syntax
  elseBody? : Option Syntax

public abbrev ConditionalFmt := Syntax → FmtM (Option Conditional)

public unsafe builtin_initialize conditionalFmtAttribute : KeyedDeclsAttribute ConditionalFmt ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_conditional_fmt
    name := `conditional_fmt
    descr := "Register an Fmt conditional formatter for a syntax node kind."
    valueTypeName := `Lean.Fmt.ConditionalFmt
    evalKey := evalFmtAttributeKey `conditional_fmt
  }

/-- Binders partitioned into layout groups, as produced by `groupBinders`. -/
public abbrev BinderGroups := Array (Array (Array Syntax))

public inductive QuantifierBinders where
  | binders (group : BinderGroups)
  | pred (lhs : Syntax) (rhs : TSyntax `binderPred)

public structure QuantifierHeadComponents where
  quantifier : Syntax
  binders : QuantifierBinders
  typeAscriptionTk? : Option Syntax
  type? : Option Syntax
  commaTk : Syntax

public structure QuantifierComponents extends QuantifierHeadComponents where
  body : Syntax

public abbrev QuantifierFmt := Syntax → Option QuantifierComponents

public unsafe builtin_initialize quantifierFmtAttribute : KeyedDeclsAttribute QuantifierFmt ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_quantifier_fmt
    name := `quantifier_fmt
    descr := "Register an Fmt quantifier formatter for a syntax node kind."
    valueTypeName := `Lean.Fmt.QuantifierFmt
    evalKey := evalFmtAttributeKey `quantifier_fmt
  }
