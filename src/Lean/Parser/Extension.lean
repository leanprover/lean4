/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Basic
import Lean.Compiler.InitAttr
import Lean.ScopedEnvExtension
import Lean.DocString

/-! Extensible parsing via attributes -/

namespace Lean
namespace Parser

builtin_initialize builtinTokenTable : IO.Ref TokenTable ← IO.mkRef {}

/- Global table with all SyntaxNodeKind's -/
builtin_initialize builtinSyntaxNodeKindSetRef : IO.Ref SyntaxNodeKindSet ← IO.mkRef {}

def registerBuiltinNodeKind (k : SyntaxNodeKind) : IO Unit :=
  builtinSyntaxNodeKindSetRef.modify fun s => s.insert k

builtin_initialize
  registerBuiltinNodeKind choiceKind
  registerBuiltinNodeKind identKind
  registerBuiltinNodeKind strLitKind
  registerBuiltinNodeKind numLitKind
  registerBuiltinNodeKind scientificLitKind
  registerBuiltinNodeKind charLitKind
  registerBuiltinNodeKind nameLitKind

builtin_initialize builtinParserCategoriesRef : IO.Ref ParserCategories ← IO.mkRef {}

private def throwParserCategoryAlreadyDefined {α} (catName : Name) : ExceptT String Id α :=
  throw s!"parser category '{catName}' has already been defined"

private def addParserCategoryCore (categories : ParserCategories) (catName : Name) (initial : ParserCategory) : Except String ParserCategories :=
  if categories.contains catName then
    throwParserCategoryAlreadyDefined catName
  else
    pure $ categories.insert catName initial

/-- All builtin parser categories are Pratt's parsers -/

private def addBuiltinParserCategory (catName declName : Name) (behavior : LeadingIdentBehavior) : IO Unit := do
  let categories ← builtinParserCategoriesRef.get
  let categories ← IO.ofExcept $ addParserCategoryCore categories catName { declName, behavior }
  builtinParserCategoriesRef.set categories

namespace ParserExtension

inductive OLeanEntry where
  | token     (val : Token) : OLeanEntry
  | kind      (val : SyntaxNodeKind) : OLeanEntry
  | category  (catName : Name) (declName : Name) (behavior : LeadingIdentBehavior)
  | parser    (catName : Name) (declName : Name) (prio : Nat) : OLeanEntry
  deriving Inhabited

inductive Entry where
  | token     (val : Token) : Entry
  | kind      (val : SyntaxNodeKind) : Entry
  | category  (catName : Name) (declName : Name) (behavior : LeadingIdentBehavior)
  | parser    (catName : Name) (declName : Name) (leading : Bool) (p : Parser) (prio : Nat) : Entry
  deriving Inhabited

def Entry.toOLeanEntry : Entry → OLeanEntry
  | token v             => OLeanEntry.token v
  | kind v              => OLeanEntry.kind v
  | category c d b      => OLeanEntry.category c d b
  | parser c d _ _ prio => OLeanEntry.parser c d prio

structure State where
  tokens      : TokenTable := {}
  kinds       : SyntaxNodeKindSet := {}
  categories  : ParserCategories := {}
  deriving Inhabited

end ParserExtension

open ParserExtension in
abbrev ParserExtension := ScopedEnvExtension OLeanEntry Entry State

private def ParserExtension.mkInitial : IO ParserExtension.State := do
  let tokens     ← builtinTokenTable.get
  let kinds      ← builtinSyntaxNodeKindSetRef.get
  let categories ← builtinParserCategoriesRef.get
  pure { tokens := tokens, kinds := kinds, categories := categories }

private def addTokenConfig (tokens : TokenTable) (tk : Token) : Except String TokenTable := do
  if tk == "" then throw "invalid empty symbol"
  else match tokens.find? tk with
    | none   => pure $ tokens.insert tk tk
    | some _ => pure tokens

def throwUnknownParserCategory {α} (catName : Name) : ExceptT String Id α :=
  throw s!"unknown parser category '{catName}'"

abbrev getCategory (categories : ParserCategories) (catName : Name) : Option ParserCategory :=
  categories.find? catName

def addLeadingParser (categories : ParserCategories) (catName declName : Name) (p : Parser) (prio : Nat) : Except String ParserCategories :=
  match getCategory categories catName with
  | none     =>
    throwUnknownParserCategory catName
  | some cat =>
    let kinds := cat.kinds.insert declName
    let addTokens (tks : List Token) : Except String ParserCategories :=
      let tks    := tks.map Name.mkSimple
      let tables := tks.eraseDups.foldl (init := cat.tables) fun tables tk =>
        { tables with leadingTable := tables.leadingTable.insert tk (p, prio) }
      pure $ categories.insert catName { cat with kinds, tables }
    match p.info.firstTokens with
    | FirstTokens.tokens tks    => addTokens tks
    | FirstTokens.optTokens tks => addTokens tks
    | _ =>
      let tables := { cat.tables with leadingParsers := (p, prio) :: cat.tables.leadingParsers }
      pure $ categories.insert catName { cat with kinds, tables }

private def addTrailingParserAux (tables : PrattParsingTables) (p : TrailingParser) (prio : Nat) : PrattParsingTables :=
  let addTokens (tks : List Token) : PrattParsingTables :=
    let tks := tks.map fun tk => Name.mkSimple tk
    tks.eraseDups.foldl (init := tables) fun tables tk =>
      { tables with trailingTable := tables.trailingTable.insert tk (p, prio) }
  match p.info.firstTokens with
  | FirstTokens.tokens tks    => addTokens tks
  | FirstTokens.optTokens tks => addTokens tks
  | _                         => { tables with trailingParsers := (p, prio) :: tables.trailingParsers }

def addTrailingParser (categories : ParserCategories) (catName declName : Name) (p : TrailingParser) (prio : Nat) : Except String ParserCategories :=
  match getCategory categories catName with
  | none     => throwUnknownParserCategory catName
  | some cat =>
    let kinds := cat.kinds.insert declName
    let tables := addTrailingParserAux cat.tables p prio
    pure $ categories.insert catName { cat with kinds, tables }

def addParser (categories : ParserCategories) (catName declName : Name)
    (leading : Bool) (p : Parser) (prio : Nat) : Except String ParserCategories := do
  match leading, p with
  | true, p  => addLeadingParser categories catName declName p prio
  | false, p => addTrailingParser categories catName declName p prio

def addParserTokens (tokenTable : TokenTable) (info : ParserInfo) : Except String TokenTable :=
  let newTokens := info.collectTokens []
  newTokens.foldlM addTokenConfig tokenTable

private def updateBuiltinTokens (info : ParserInfo) (declName : Name) : IO Unit := do
  let tokenTable ← builtinTokenTable.swap {}
  match addParserTokens tokenTable info with
  | Except.ok tokenTable => builtinTokenTable.set tokenTable
  | Except.error msg     => throw (IO.userError s!"invalid builtin parser '{declName}', {msg}")

def ParserExtension.addEntryImpl (s : State) (e : Entry) : State :=
  match e with
  | Entry.token tk =>
    match addTokenConfig s.tokens tk with
    | Except.ok tokens => { s with tokens }
    | _                => unreachable!
  | Entry.kind k =>
    { s with kinds := s.kinds.insert k }
  | Entry.category catName declName behavior =>
    if s.categories.contains catName then s
    else { s with
           categories := s.categories.insert catName { declName, behavior } }
  | Entry.parser catName declName leading parser prio =>
    match addParser s.categories catName declName leading parser prio with
    | Except.ok categories => { s with categories }
    | _ => unreachable!

/-- Parser aliases for making `ParserDescr` extensible -/
inductive AliasValue (α : Type) where
  | const  (p : α)
  | unary  (p : α → α)
  | binary (p : α → α → α)

abbrev AliasTable (α) := NameMap (AliasValue α)

def registerAliasCore {α} (mapRef : IO.Ref (AliasTable α)) (aliasName : Name) (value : AliasValue α) : IO Unit := do
  unless (← initializing) do throw ↑"aliases can only be registered during initialization"
  if (← mapRef.get).contains aliasName then
    throw ↑s!"alias '{aliasName}' has already been declared"
  mapRef.modify (·.insert aliasName value)

def getAlias {α} (mapRef : IO.Ref (AliasTable α)) (aliasName : Name) : IO (Option (AliasValue α)) := do
  return (← mapRef.get).find? aliasName

def getConstAlias {α} (mapRef : IO.Ref (AliasTable α)) (aliasName : Name) : IO α := do
  match (← getAlias mapRef aliasName) with
  | some (AliasValue.const v)  => pure v
  | some (AliasValue.unary _)  => throw ↑s!"parser '{aliasName}' is not a constant, it takes one argument"
  | some (AliasValue.binary _) => throw ↑s!"parser '{aliasName}' is not a constant, it takes two arguments"
  | none   => throw ↑s!"parser '{aliasName}' was not found"

def getUnaryAlias {α} (mapRef : IO.Ref (AliasTable α)) (aliasName : Name) : IO (α → α) := do
  match (← getAlias mapRef aliasName) with
  | some (AliasValue.unary v) => pure v
  | some _ => throw ↑s!"parser '{aliasName}' does not take one argument"
  | none   => throw ↑s!"parser '{aliasName}' was not found"

def getBinaryAlias {α} (mapRef : IO.Ref (AliasTable α)) (aliasName : Name) : IO (α → α → α) := do
  match (← getAlias mapRef aliasName) with
  | some (AliasValue.binary v) => pure v
  | some _ => throw ↑s!"parser '{aliasName}' does not take two arguments"
  | none   => throw ↑s!"parser '{aliasName}' was not found"

abbrev ParserAliasValue := AliasValue Parser

structure ParserAliasInfo where
  declName : Name := .anonymous
  /-- Number of syntax nodes produced by this parser. `none` means "sum of input sizes". -/
  stackSz? : Option Nat := some 1
  /-- Whether arguments should be wrapped in `group(·)` if they do not produce exactly one syntax node. -/
  autoGroupArgs : Bool := stackSz?.isSome

builtin_initialize parserAliasesRef : IO.Ref (NameMap ParserAliasValue) ← IO.mkRef {}
builtin_initialize parserAlias2kindRef : IO.Ref (NameMap SyntaxNodeKind) ← IO.mkRef {}
builtin_initialize parserAliases2infoRef : IO.Ref (NameMap ParserAliasInfo) ← IO.mkRef {}

def getParserAliasInfo (aliasName : Name) : IO ParserAliasInfo := do
  return (← parserAliases2infoRef.get).findD aliasName {}

-- Later, we define macro `register_parser_alias` which registers a parser, formatter and parenthesizer
def registerAlias (aliasName declName : Name) (p : ParserAliasValue) (kind? : Option SyntaxNodeKind := none) (info : ParserAliasInfo := {}) : IO Unit := do
  registerAliasCore parserAliasesRef aliasName p
  if let some kind := kind? then
    parserAlias2kindRef.modify (·.insert aliasName kind)
  parserAliases2infoRef.modify (·.insert aliasName { info with declName })

instance : Coe Parser ParserAliasValue := { coe := AliasValue.const }
instance : Coe (Parser → Parser) ParserAliasValue := { coe := AliasValue.unary }
instance : Coe (Parser → Parser → Parser) ParserAliasValue := { coe := AliasValue.binary }

def isParserAlias (aliasName : Name) : IO Bool := do
  match (← getAlias parserAliasesRef aliasName) with
  | some _ => pure true
  | _      => pure false

def getSyntaxKindOfParserAlias? (aliasName : Name) : IO (Option SyntaxNodeKind) :=
  return (← parserAlias2kindRef.get).find? aliasName

def ensureUnaryParserAlias (aliasName : Name) : IO Unit :=
  discard $ getUnaryAlias parserAliasesRef aliasName

def ensureBinaryParserAlias (aliasName : Name) : IO Unit :=
  discard $ getBinaryAlias parserAliasesRef aliasName

def ensureConstantParserAlias (aliasName : Name) : IO Unit :=
  discard $ getConstAlias parserAliasesRef aliasName

unsafe def mkParserOfConstantUnsafe (constName : Name) (compileParserDescr : ParserDescr → ImportM Parser) : ImportM (Bool × Parser) := do
  let env  := (← read).env
  let opts := (← read).opts
  match env.find? constName with
  | none      => throw ↑s!"unknown constant '{constName}'"
  | some info =>
    match info.type with
    | Expr.const `Lean.Parser.TrailingParser _ =>
      let p ← IO.ofExcept $ env.evalConst Parser opts constName
      pure ⟨false, p⟩
    | Expr.const `Lean.Parser.Parser _ =>
      let p ← IO.ofExcept $ env.evalConst Parser opts constName
      pure ⟨true, p⟩
    | Expr.const `Lean.ParserDescr _ =>
      let d ← IO.ofExcept $ env.evalConst ParserDescr opts constName
      let p ← compileParserDescr d
      pure ⟨true, p⟩
    | Expr.const `Lean.TrailingParserDescr _ =>
      let d ← IO.ofExcept $ env.evalConst TrailingParserDescr opts constName
      let p ← compileParserDescr d
      pure ⟨false, p⟩
    | _ => throw ↑s!"unexpected parser type at '{constName}' (`ParserDescr`, `TrailingParserDescr`, `Parser` or `TrailingParser` expected)"

@[implemented_by mkParserOfConstantUnsafe]
opaque mkParserOfConstantAux (constName : Name) (compileParserDescr : ParserDescr → ImportM Parser) : ImportM (Bool × Parser)

partial def compileParserDescr (categories : ParserCategories) (d : ParserDescr) : ImportM Parser :=
  let rec visit : ParserDescr → ImportM Parser
    | ParserDescr.const n                             => getConstAlias parserAliasesRef n
    | ParserDescr.unary n d                           => return (← getUnaryAlias parserAliasesRef n) (← visit d)
    | ParserDescr.binary n d₁ d₂                      => return (← getBinaryAlias parserAliasesRef n) (← visit d₁) (← visit d₂)
    | ParserDescr.node k prec d                       => return leadingNode k prec (← visit d)
    | ParserDescr.nodeWithAntiquot n k d              => return withCache k (nodeWithAntiquot n k (← visit d) (anonymous := true))
    | ParserDescr.sepBy p sep psep trail              => return sepBy (← visit p) sep (← visit psep) trail
    | ParserDescr.sepBy1 p sep psep trail             => return sepBy1 (← visit p) sep (← visit psep) trail
    | ParserDescr.trailingNode k prec lhsPrec d       => return trailingNode k prec lhsPrec (← visit d)
    | ParserDescr.symbol tk                           => return symbol tk
    | ParserDescr.nonReservedSymbol tk includeIdent   => return nonReservedSymbol tk includeIdent
    | ParserDescr.parser constName                    => do
      let (_, p) ← mkParserOfConstantAux constName visit;
      pure p
    | ParserDescr.cat catName prec                    =>
      match getCategory categories catName with
      | some _ => pure $ categoryParser catName prec
      | none   => IO.ofExcept $ throwUnknownParserCategory catName
  visit d

def mkParserOfConstant (categories : ParserCategories) (constName : Name) : ImportM (Bool × Parser) :=
  mkParserOfConstantAux constName (compileParserDescr categories)

structure ParserAttributeHook where
  /-- Called after a parser attribute is applied to a declaration. -/
  postAdd (catName : Name) (declName : Name) (builtin : Bool) : AttrM Unit

builtin_initialize parserAttributeHooks : IO.Ref (List ParserAttributeHook) ← IO.mkRef {}

def registerParserAttributeHook (hook : ParserAttributeHook) : IO Unit := do
  parserAttributeHooks.modify fun hooks => hook::hooks

def runParserAttributeHooks (catName : Name) (declName : Name) (builtin : Bool) : AttrM Unit := do
  let hooks ← parserAttributeHooks.get
  hooks.forM fun hook => hook.postAdd catName declName builtin

builtin_initialize
  registerBuiltinAttribute {
    name  := `run_builtin_parser_attribute_hooks
    descr := "explicitly run hooks normally activated by builtin parser attributes"
    add   := fun decl stx _ => do
      Attribute.Builtin.ensureNoArgs stx
      runParserAttributeHooks Name.anonymous decl (builtin := true)
  }

builtin_initialize
  registerBuiltinAttribute {
    name  := `run_parser_attribute_hooks
    descr := "explicitly run hooks normally activated by parser attributes"
    add   := fun decl stx _ => do
      Attribute.Builtin.ensureNoArgs stx
      runParserAttributeHooks Name.anonymous decl (builtin := false)
  }

private def ParserExtension.OLeanEntry.toEntry (s : State) : OLeanEntry → ImportM Entry
  | token tk       => return Entry.token tk
  | kind k         => return Entry.kind k
  | category c d l => return Entry.category c d l
  | parser catName declName prio => do
    let (leading, p) ← mkParserOfConstant s.categories declName
    return Entry.parser catName declName leading p prio

builtin_initialize parserExtension : ParserExtension ←
  registerScopedEnvExtension {
    mkInitial       := ParserExtension.mkInitial
    addEntry        := ParserExtension.addEntryImpl
    toOLeanEntry    := ParserExtension.Entry.toOLeanEntry
    ofOLeanEntry    := ParserExtension.OLeanEntry.toEntry
  }

def isParserCategory (env : Environment) (catName : Name) : Bool :=
  (parserExtension.getState env).categories.contains catName

def addParserCategory (env : Environment) (catName declName : Name) (behavior : LeadingIdentBehavior) : Except String Environment := do
  if isParserCategory env catName then
    throwParserCategoryAlreadyDefined catName
  else
    return parserExtension.addEntry env <| ParserExtension.Entry.category catName declName behavior

def leadingIdentBehavior (env : Environment) (catName : Name) : LeadingIdentBehavior :=
  match getCategory (parserExtension.getState env).categories catName with
  | none     => LeadingIdentBehavior.default
  | some cat => cat.behavior

unsafe def evalParserConstUnsafe (declName : Name) : ParserFn := fun ctx s => unsafeBaseIO do
  let categories := (parserExtension.getState ctx.env).categories
  match (← (mkParserOfConstant categories declName { env := ctx.env, opts := ctx.options }).toBaseIO) with
  | .ok (_, p) =>
    -- We should manually register `p`'s tokens before invoking it as it might not be part of any syntax category (yet)
    return adaptUncacheableContextFn (fun ctx => { ctx with tokens := p.info.collectTokens [] |>.foldl (fun tks tk => tks.insert tk tk) ctx.tokens }) p.fn ctx s
  | .error e   => return s.mkUnexpectedError e.toString

@[implemented_by evalParserConstUnsafe]
opaque evalParserConst (declName : Name) : ParserFn

register_builtin_option internal.parseQuotWithCurrentStage : Bool := {
  defValue := false
  group    := "internal"
  descr    := "(Lean bootstrapping) use parsers from the current stage inside quotations"
}

/-- Run `declName` if possible and inside a quotation, or else `p`. The `ParserInfo` will always be taken from `p`. -/
def evalInsideQuot (declName : Name) : Parser → Parser := withFn fun f c s =>
  if c.quotDepth > 0 && !c.suppressInsideQuot && internal.parseQuotWithCurrentStage.get c.options && c.env.contains declName then
    evalParserConst declName c s
  else
    f c s

def addBuiltinParser (catName : Name) (declName : Name) (leading : Bool) (p : Parser) (prio : Nat) : IO Unit := do
  let p := evalInsideQuot declName p
  let categories ← builtinParserCategoriesRef.get
  let categories ← IO.ofExcept $ addParser categories catName declName leading p prio
  builtinParserCategoriesRef.set categories
  builtinSyntaxNodeKindSetRef.modify p.info.collectKinds
  updateBuiltinTokens p.info declName

def addBuiltinLeadingParser (catName : Name) (declName : Name) (p : Parser) (prio : Nat) : IO Unit :=
  addBuiltinParser catName declName true p prio

def addBuiltinTrailingParser (catName : Name) (declName : Name) (p : TrailingParser) (prio : Nat) : IO Unit :=
  addBuiltinParser catName declName false p prio

def mkCategoryAntiquotParser (kind : Name) : Parser :=
  mkAntiquot kind.toString kind (isPseudoKind := true)

-- helper decl to work around inlining issue https://github.com/leanprover/lean4/commit/3f6de2af06dd9a25f62294129f64bc05a29ea912#r41340377
@[inline] private def mkCategoryAntiquotParserFn (kind : Name) : ParserFn :=
  (mkCategoryAntiquotParser kind).fn

def categoryParserFnImpl (catName : Name) : ParserFn := fun ctx s =>
  let catName := if catName == `syntax then `stx else catName -- temporary Hack
  let categories := (parserExtension.getState ctx.env).categories
  match getCategory categories catName with
  | some cat =>
    prattParser catName cat.tables cat.behavior (mkCategoryAntiquotParserFn catName) ctx s
  | none     => s.mkUnexpectedError ("unknown parser category '" ++ toString catName ++ "'")

builtin_initialize
  categoryParserFnRef.set categoryParserFnImpl

def addToken (tk : Token) (kind : AttributeKind) : AttrM Unit := do
  -- Recall that `ParserExtension.addEntry` is pure, and assumes `addTokenConfig` does not fail.
  -- So, we must run it here to handle exception.
  discard <| ofExcept <| addTokenConfig (parserExtension.getState (← getEnv)).tokens tk
  parserExtension.add (ParserExtension.Entry.token tk) kind

def addSyntaxNodeKind (env : Environment) (k : SyntaxNodeKind) : Environment :=
  parserExtension.addEntry env <| ParserExtension.Entry.kind k

def isValidSyntaxNodeKind (env : Environment) (k : SyntaxNodeKind) : Bool :=
  let kinds := (parserExtension.getState env).kinds
  -- accept any constant in stage 1 (i.e. when compiled by stage 0) so that
  -- we can add a built-in parser and its elaborator in the same stage
  kinds.contains k || (Internal.isStage0 () && env.contains k)

def getSyntaxNodeKinds (env : Environment) : List SyntaxNodeKind :=
  let kinds := (parserExtension.getState env).kinds
  kinds.foldl (fun ks k _ => k::ks) []

def getTokenTable (env : Environment) : TokenTable :=
  (parserExtension.getState env).tokens

def mkInputContext (input : String) (fileName : String) : InputContext := {
  input    := input,
  fileName := fileName,
  fileMap  := input.toFileMap
}

def mkParserState (input : String) : ParserState :=
  { cache := initCacheForInput input }

/-- convenience function for testing -/
def runParserCategory (env : Environment) (catName : Name) (input : String) (fileName := "<input>") : Except String Syntax :=
  let p := andthenFn whitespace (categoryParserFnImpl catName)
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if input.atEnd s.pos then
    Except.ok s.stxStack.back
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)

def declareBuiltinParser (addFnName : Name) (catName : Name) (declName : Name) (prio : Nat) : CoreM Unit :=
  let val := mkAppN (mkConst addFnName) #[toExpr catName, toExpr declName, mkConst declName, mkRawNatLit prio]
  declareBuiltin declName val

def declareLeadingBuiltinParser (catName : Name) (declName : Name) (prio : Nat) : CoreM Unit :=
  declareBuiltinParser `Lean.Parser.addBuiltinLeadingParser catName declName prio

def declareTrailingBuiltinParser (catName : Name) (declName : Name) (prio : Nat) : CoreM Unit :=
  declareBuiltinParser `Lean.Parser.addBuiltinTrailingParser catName declName prio

def getParserPriority (args : Syntax) : Except String Nat :=
  match args.getNumArgs with
  | 0 => pure 0
  | 1 => match (args.getArg 0).isNatLit? with
    | some prio => pure prio
    | none => throw "invalid parser attribute, numeral expected"
  | _ => throw "invalid parser attribute, no argument or numeral expected"

private def BuiltinParserAttribute.add (attrName : Name) (catName : Name)
    (declName : Name) (stx : Syntax) (kind : AttributeKind) : AttrM Unit := do
  let prio ← Attribute.Builtin.getPrio stx
  unless kind == AttributeKind.global do throwError "invalid attribute '{attrName}', must be global"
  let decl ← getConstInfo declName
  match decl.type with
  | Expr.const `Lean.Parser.TrailingParser _ =>
    declareTrailingBuiltinParser catName declName prio
  | Expr.const `Lean.Parser.Parser _ =>
    declareLeadingBuiltinParser catName declName prio
  | _ => throwError "unexpected parser type at '{declName}' (`Parser` or `TrailingParser` expected)"
  if let some doc ← findDocString? (← getEnv) declName (includeBuiltin := false) then
    declareBuiltin (declName ++ `docString) (mkAppN (mkConst ``addBuiltinDocString) #[toExpr declName, toExpr doc])
  if let some declRanges ← findDeclarationRanges? declName then
    declareBuiltin (declName ++ `declRange) (mkAppN (mkConst ``addBuiltinDeclarationRanges) #[toExpr declName, toExpr declRanges])
  runParserAttributeHooks catName declName (builtin := true)

/--
The parsing tables for builtin parsers are "stored" in the extracted source code.
-/
def registerBuiltinParserAttribute (attrName declName : Name)
    (behavior := LeadingIdentBehavior.default) : IO Unit := do
  let .str ``Lean.Parser.Category s := declName
    | throw (IO.userError "`declName` should be in Lean.Parser.Category")
  let catName := Name.mkSimple s
  addBuiltinParserCategory catName declName behavior
  registerBuiltinAttribute {
    ref             := declName
    name            := attrName
    descr           := "Builtin parser"
    add             := fun declName stx kind => liftM $ BuiltinParserAttribute.add attrName catName declName stx kind
    applicationTime := AttributeApplicationTime.afterCompilation
  }

private def ParserAttribute.add (_attrName : Name) (catName : Name) (declName : Name) (stx : Syntax) (attrKind : AttributeKind) : AttrM Unit := do
  let prio ← Attribute.Builtin.getPrio stx
  let env ← getEnv
  let categories := (parserExtension.getState env).categories
  let p ← mkParserOfConstant categories declName
  let leading    := p.1
  let parser     := p.2
  let tokens     := parser.info.collectTokens []
  tokens.forM fun token => do
    try
      addToken token attrKind
    catch
      | Exception.error _   msg => throwError "invalid parser '{declName}', {msg}"
      | ex => throw ex
  let kinds := parser.info.collectKinds {}
  kinds.forM fun kind _ => modifyEnv fun env => addSyntaxNodeKind env kind
  let entry := ParserExtension.Entry.parser catName declName leading parser prio
  match addParser categories catName declName leading parser prio with
  | Except.error ex => throwError ex
  | Except.ok _     => parserExtension.add entry attrKind
  runParserAttributeHooks catName declName (builtin := false)

def mkParserAttributeImpl (attrName catName : Name) (ref : Name := by exact decl_name%) : AttributeImpl where
  ref                       := ref
  name                      := attrName
  descr                     := "parser"
  add declName stx attrKind := ParserAttribute.add attrName catName declName stx attrKind
  applicationTime           := AttributeApplicationTime.afterCompilation

/-- A builtin parser attribute that can be extended by users. -/
def registerBuiltinDynamicParserAttribute (attrName catName : Name) (ref : Name := by exact decl_name%) : IO Unit := do
  registerBuiltinAttribute (mkParserAttributeImpl attrName catName ref)

builtin_initialize
  registerAttributeImplBuilder `parserAttr fun ref args =>
    match args with
    | [DataValue.ofName attrName, DataValue.ofName catName] => pure $ mkParserAttributeImpl attrName catName ref
    | _ => throw "invalid parser attribute implementation builder arguments"

def registerParserCategory (env : Environment) (attrName catName : Name)
    (behavior := LeadingIdentBehavior.default) (ref : Name := by exact decl_name%) : IO Environment := do
  let env ← IO.ofExcept $ addParserCategory env catName ref behavior
  registerAttributeOfBuilder env `parserAttr ref [DataValue.ofName attrName, DataValue.ofName catName]

-- declare `term_parser` here since it is used everywhere via antiquotations

builtin_initialize registerBuiltinParserAttribute `builtin_term_parser ``Category.term

builtin_initialize registerBuiltinDynamicParserAttribute `term_parser `term

-- declare `command_parser` to break cyclic dependency
builtin_initialize registerBuiltinParserAttribute `builtin_command_parser ``Category.command

builtin_initialize registerBuiltinDynamicParserAttribute `command_parser `command

@[inline] def commandParser (rbp : Nat := 0) : Parser :=
  categoryParser `command rbp

private def withNamespaces (ids : Array Name) (addOpenSimple : Bool) : ParserFn → ParserFn := adaptUncacheableContextFn fun c =>
  let c := ids.foldl (init := c) fun c id =>
    let nss := ResolveName.resolveNamespace c.env c.currNamespace c.openDecls id
    let (env, openDecls) := nss.foldl (init := (c.env, c.openDecls)) fun (env, openDecls) ns =>
      let openDecls := if addOpenSimple then OpenDecl.simple ns [] :: openDecls else openDecls
      let env := parserExtension.activateScoped env ns
      (env, openDecls)
    { c with env, openDecls }
  let tokens := parserExtension.getState c.env |>.tokens
  { c with tokens }

def withOpenDeclFnCore (openDeclStx : Syntax) (p : ParserFn) : ParserFn := fun c s =>
  if openDeclStx.getKind == `Lean.Parser.Command.openSimple then
    withNamespaces (openDeclStx[0].getArgs.map fun stx => stx.getId) (addOpenSimple := true) p c s
  else if openDeclStx.getKind == `Lean.Parser.Command.openScoped then
    withNamespaces (openDeclStx[1].getArgs.map fun stx => stx.getId) (addOpenSimple := false) p c s
  else if openDeclStx.getKind == `Lean.Parser.Command.openOnly then
    -- It does not activate scoped attributes, nor affects namespace resolution
    p c s
  else if openDeclStx.getKind == `Lean.Parser.Command.openHiding then
    -- TODO: it does not activate scoped attributes, but it affects namespaces resolution of open decls parsed by `p`.
    p c s
  else
    p c s

/-- If the parsing stack is of the form `#[.., openCommand]`, we process the open command, and execute `p` -/
def withOpenFn (p : ParserFn) : ParserFn := fun c s =>
  if s.stxStack.size > 0 then
    let stx := s.stxStack.back
    if stx.getKind == `Lean.Parser.Command.open then
      withOpenDeclFnCore stx[1] p c s
    else
      p c s
  else
    p c s


@[inline] def withOpen : Parser → Parser := withFn withOpenFn

/-- If the parsing stack is of the form `#[.., openDecl]`, we process the open declaration, and execute `p` -/
def withOpenDeclFn (p : ParserFn) : ParserFn := fun c s =>
  if s.stxStack.size > 0 then
    let stx := s.stxStack.back
    withOpenDeclFnCore stx p c s
  else
    p c s

@[inline] def withOpenDecl : Parser → Parser := withFn withOpenDeclFn

inductive ParserName
  | category (cat : Name)
  | parser (decl : Name) (isDescr : Bool)
  -- TODO(gabriel): add parser aliases (this is blocked on doing IO in parsers)
  deriving Repr

/-- Resolve the given parser name and return a list of candidates. -/
def resolveParserNameCore (env : Environment) (currNamespace : Name)
    (openDecls : List OpenDecl) (ident : Ident) : List ParserName := Id.run do
  let ⟨.ident (val := val) (preresolved := pre) ..⟩ := ident | return []

  let rec isParser (name : Name) : Option Bool :=
    (env.find? name).bind fun ci =>
      match ci.type with
      | .const ``Parser _ | .const ``TrailingParser _ => some false
      | .const ``ParserDescr _ | .const ``TrailingParserDescr _ => some true
      | _ => none

  for pre in pre do
    if let .decl n [] := pre then
      if let some isDescr := isParser n then
        return [.parser n isDescr]

  let erased := val.eraseMacroScopes

  if isParserCategory env erased then
    return [.category erased]

  ResolveName.resolveGlobalName env currNamespace openDecls val |>.filterMap fun
      | (name, []) => (isParser name).map fun isDescr => .parser name isDescr
      | _ => none

/-- Resolve the given parser name and return a list of candidates. -/
def ParserContext.resolveParserName (ctx : ParserContext) (id : Ident) : List ParserName :=
  Parser.resolveParserNameCore ctx.env ctx.currNamespace ctx.openDecls id

/-- Resolve the given parser name and return a list of candidates. -/
def resolveParserName (id : Ident) : CoreM (List ParserName) :=
  return resolveParserNameCore (← getEnv) (← getCurrNamespace) (← getOpenDecls) id

def parserOfStackFn (offset : Nat) : ParserFn := fun ctx s => Id.run do
  let stack := s.stxStack
  if stack.size < offset + 1 then
    return s.mkUnexpectedError ("failed to determine parser using syntax stack, stack is too small")
  let parserName@(.ident ..) := stack.get! (stack.size - offset - 1)
    | s.mkUnexpectedError ("failed to determine parser using syntax stack, the specified element on the stack is not an identifier")
  match ctx.resolveParserName ⟨parserName⟩ with
  | [.category cat] =>
    categoryParserFn cat ctx s
  | [.parser parserName _] =>
    let iniSz := s.stackSize
    let s := adaptUncacheableContextFn (fun ctx =>
      if !internal.parseQuotWithCurrentStage.get ctx.options then
        -- static quotations such as `(e) do not use the interpreter unless the above option is set,
        -- so for consistency neither should dynamic quotations using this function
        { ctx with options := ctx.options.setBool `interpreter.prefer_native true }
      else ctx) (evalParserConst parserName) ctx s
    if !s.hasError && s.stackSize != iniSz + 1 then
      s.mkUnexpectedError "expected parser to return exactly one syntax object"
    else
      s
  | _::_::_ => s.mkUnexpectedError s!"ambiguous parser name {parserName}"
  | [] => s.mkUnexpectedError s!"unknown parser {parserName}"

def parserOfStack (offset : Nat) (prec : Nat := 0) : Parser where
  fn := adaptCacheableContextFn ({ · with prec }) (parserOfStackFn offset)

end Parser
end Lean
