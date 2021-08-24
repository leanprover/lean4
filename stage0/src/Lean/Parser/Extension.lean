/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.ResolveName
import Lean.ScopedEnvExtension
import Lean.Parser.Basic
import Lean.Parser.StrInterpolation
import Lean.KeyedDeclsAttribute

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

private def addBuiltinParserCategory (catName : Name) (behavior : LeadingIdentBehavior) : IO Unit := do
  let categories ← builtinParserCategoriesRef.get
  let categories ← IO.ofExcept $ addParserCategoryCore categories catName { tables := {}, behavior := behavior}
  builtinParserCategoriesRef.set categories

namespace ParserExtension

inductive OLeanEntry where
  | token     (val : Token) : OLeanEntry
  | kind      (val : SyntaxNodeKind) : OLeanEntry
  | category  (catName : Name) (behavior : LeadingIdentBehavior)
  | parser    (catName : Name) (declName : Name) (prio : Nat) : OLeanEntry
  deriving Inhabited

inductive Entry where
  | token     (val : Token) : Entry
  | kind      (val : SyntaxNodeKind) : Entry
  | category  (catName : Name) (behavior : LeadingIdentBehavior)
  | parser    (catName : Name) (declName : Name) (leading : Bool) (p : Parser) (prio : Nat) : Entry
  deriving Inhabited

def Entry.toOLeanEntry : Entry → OLeanEntry
  | token v             => OLeanEntry.token v
  | kind v              => OLeanEntry.kind v
  | category c b        => OLeanEntry.category c b
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

def addLeadingParser (categories : ParserCategories) (catName : Name) (parserName : Name) (p : Parser) (prio : Nat) : Except String ParserCategories :=
  match getCategory categories catName with
  | none     =>
    throwUnknownParserCategory catName
  | some cat =>
    let addTokens (tks : List Token) : Except String ParserCategories :=
      let tks    := tks.map $ fun tk => Name.mkSimple tk
      let tables := tks.eraseDups.foldl (fun (tables : PrattParsingTables) tk => { tables with leadingTable := tables.leadingTable.insert tk (p, prio) }) cat.tables
      pure $ categories.insert catName { cat with tables := tables }
    match p.info.firstTokens with
    | FirstTokens.tokens tks    => addTokens tks
    | FirstTokens.optTokens tks => addTokens tks
    | _ =>
      let tables := { cat.tables with leadingParsers := (p, prio) :: cat.tables.leadingParsers }
      pure $ categories.insert catName { cat with tables := tables }

private def addTrailingParserAux (tables : PrattParsingTables) (p : TrailingParser) (prio : Nat) : PrattParsingTables :=
  let addTokens (tks : List Token) : PrattParsingTables :=
    let tks := tks.map fun tk => Name.mkSimple tk
    tks.eraseDups.foldl (fun (tables : PrattParsingTables) tk => { tables with trailingTable := tables.trailingTable.insert tk (p, prio) }) tables
  match p.info.firstTokens with
  | FirstTokens.tokens tks    => addTokens tks
  | FirstTokens.optTokens tks => addTokens tks
  | _                         => { tables with trailingParsers := (p, prio) :: tables.trailingParsers }

def addTrailingParser (categories : ParserCategories) (catName : Name) (p : TrailingParser) (prio : Nat) : Except String ParserCategories :=
  match getCategory categories catName with
  | none     => throwUnknownParserCategory catName
  | some cat => pure $ categories.insert catName { cat with tables := addTrailingParserAux cat.tables p prio }

def addParser (categories : ParserCategories) (catName : Name) (declName : Name) (leading : Bool) (p : Parser) (prio : Nat) : Except String ParserCategories :=
  match leading, p with
  | true, p  => addLeadingParser categories catName declName p prio
  | false, p => addTrailingParser categories catName p prio

def addParserTokens (tokenTable : TokenTable) (info : ParserInfo) : Except String TokenTable :=
  let newTokens := info.collectTokens []
  newTokens.foldlM addTokenConfig tokenTable

private def updateBuiltinTokens (info : ParserInfo) (declName : Name) : IO Unit := do
  let tokenTable ← builtinTokenTable.swap {}
  match addParserTokens tokenTable info with
  | Except.ok tokenTable => builtinTokenTable.set tokenTable
  | Except.error msg     => throw (IO.userError s!"invalid builtin parser '{declName}', {msg}")

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

def ParserExtension.addEntryImpl (s : State) (e : Entry) : State :=
  match e with
  | Entry.token tk =>
    match addTokenConfig s.tokens tk with
    | Except.ok tokens => { s with tokens := tokens }
    | _                => unreachable!
  | Entry.kind k =>
    { s with kinds := s.kinds.insert k }
  | Entry.category catName behavior =>
    if s.categories.contains catName then s
    else { s with
           categories := s.categories.insert catName { tables := {}, behavior := behavior } }
  | Entry.parser catName declName leading parser prio =>
    match addParser s.categories catName declName leading parser prio with
    | Except.ok categories => { s with categories := categories }
    | _ => unreachable!

unsafe def mkParserOfConstantUnsafe
    (categories : ParserCategories) (constName : Name) (compileParserDescr : ParserDescr → ImportM Parser) : ImportM (Bool × Parser) := do
  let env  := (← read).env
  let opts := (← read).opts
  match env.find? constName with
  | none      => throw ↑s!"unknow constant '{constName}'"
  | some info =>
    match info.type with
    | Expr.const `Lean.Parser.TrailingParser _ _ =>
      let p ← IO.ofExcept $ env.evalConst Parser opts constName
      pure ⟨false, p⟩
    | Expr.const `Lean.Parser.Parser _ _ =>
      let p ← IO.ofExcept $ env.evalConst Parser opts constName
      pure ⟨true, p⟩
    | Expr.const `Lean.ParserDescr _ _ =>
      let d ← IO.ofExcept $ env.evalConst ParserDescr opts constName
      let p ← compileParserDescr d
      pure ⟨true, p⟩
    | Expr.const `Lean.TrailingParserDescr _ _ =>
      let d ← IO.ofExcept $ env.evalConst TrailingParserDescr opts constName
      let p ← compileParserDescr d
      pure ⟨false, p⟩
    | _ => throw ↑s!"unexpected parser type at '{constName}' (`ParserDescr`, `TrailingParserDescr`, `Parser` or `TrailingParser` expected"

@[implementedBy mkParserOfConstantUnsafe]
constant mkParserOfConstantAux
    (categories : ParserCategories) (constName : Name) (compileParserDescr : ParserDescr → ImportM Parser) : ImportM (Bool × Parser)

/- Parser aliases for making `ParserDescr` extensible -/
inductive AliasValue (α : Type) where
  | const  (p : α)
  | unary  (p : α → α)
  | binary (p : α → α → α)

abbrev AliasTable (α) := NameMap (AliasValue α)

def registerAliasCore {α} (mapRef : IO.Ref (AliasTable α)) (aliasName : Name) (value : AliasValue α) : IO Unit := do
  unless (← IO.initializing) do throw ↑"aliases can only be registered during initialization"
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

builtin_initialize parserAliasesRef : IO.Ref (NameMap ParserAliasValue) ← IO.mkRef {}

-- Later, we define macro registerParserAlias! which registers a parser, formatter and parenthesizer
def registerAlias (aliasName : Name) (p : ParserAliasValue) : IO Unit := do
  registerAliasCore parserAliasesRef aliasName p

instance : Coe Parser ParserAliasValue := { coe := AliasValue.const }
instance : Coe (Parser → Parser) ParserAliasValue := { coe := AliasValue.unary }
instance : Coe (Parser → Parser → Parser) ParserAliasValue := { coe := AliasValue.binary }

def isParserAlias (aliasName : Name) : IO Bool := do
  match (← getAlias parserAliasesRef aliasName) with
  | some _ => pure true
  | _      => pure false

def ensureUnaryParserAlias (aliasName : Name) : IO Unit :=
  discard $ getUnaryAlias parserAliasesRef aliasName

def ensureBinaryParserAlias (aliasName : Name) : IO Unit :=
  discard $ getBinaryAlias parserAliasesRef aliasName

def ensureConstantParserAlias (aliasName : Name) : IO Unit :=
  discard $ getConstAlias parserAliasesRef aliasName

partial def compileParserDescr (categories : ParserCategories) (d : ParserDescr) : ImportM Parser :=
  let rec visit : ParserDescr → ImportM Parser
    | ParserDescr.const n                             => getConstAlias parserAliasesRef n
    | ParserDescr.unary n d                           => return (← getUnaryAlias parserAliasesRef n) (← visit d)
    | ParserDescr.binary n d₁ d₂                      => return (← getBinaryAlias parserAliasesRef n) (← visit d₁) (← visit d₂)
    | ParserDescr.node k prec d                       => return leadingNode k prec (← visit d)
    | ParserDescr.nodeWithAntiquot n k d              => return nodeWithAntiquot n k (← visit d) (anonymous := true)
    | ParserDescr.sepBy p sep psep trail              => return sepBy (← visit p) sep (← visit psep) trail
    | ParserDescr.sepBy1 p sep psep trail             => return sepBy1 (← visit p) sep (← visit psep) trail
    | ParserDescr.trailingNode k prec lhsPrec d       => return trailingNode k prec lhsPrec (← visit d)
    | ParserDescr.symbol tk                           => return symbol tk
    | ParserDescr.nonReservedSymbol tk includeIdent   => return nonReservedSymbol tk includeIdent
    | ParserDescr.parser constName                    => do
      let (_, p) ← mkParserOfConstantAux categories constName visit;
      pure p
    | ParserDescr.cat catName prec                    =>
      match getCategory categories catName with
      | some _ => pure $ categoryParser catName prec
      | none   => IO.ofExcept $ throwUnknownParserCategory catName
  visit d

def mkParserOfConstant (categories : ParserCategories) (constName : Name) : ImportM (Bool × Parser) :=
  mkParserOfConstantAux categories constName (compileParserDescr categories)

structure ParserAttributeHook where
  /- Called after a parser attribute is applied to a declaration. -/
  postAdd (catName : Name) (declName : Name) (builtin : Bool) : AttrM Unit

builtin_initialize parserAttributeHooks : IO.Ref (List ParserAttributeHook) ← IO.mkRef {}

def registerParserAttributeHook (hook : ParserAttributeHook) : IO Unit := do
  parserAttributeHooks.modify fun hooks => hook::hooks

def runParserAttributeHooks (catName : Name) (declName : Name) (builtin : Bool) : AttrM Unit := do
  let hooks ← parserAttributeHooks.get
  hooks.forM fun hook => hook.postAdd catName declName builtin

builtin_initialize
  registerBuiltinAttribute {
    name  := `runBuiltinParserAttributeHooks,
    descr := "explicitly run hooks normally activated by builtin parser attributes",
    add   := fun decl stx persistent => do
      Attribute.Builtin.ensureNoArgs stx
      runParserAttributeHooks Name.anonymous decl (builtin := true)
  }

builtin_initialize
  registerBuiltinAttribute {
    name  := `runParserAttributeHooks,
    descr := "explicitly run hooks normally activated by parser attributes",
    add   := fun decl stx persistent => do
      Attribute.Builtin.ensureNoArgs stx
      runParserAttributeHooks Name.anonymous decl (builtin := false)
  }

private def ParserExtension.OLeanEntry.toEntry (s : State) : OLeanEntry → ImportM Entry
  | token tk     => return Entry.token tk
  | kind k       => return Entry.kind k
  | category c l => return Entry.category c l
  | parser catName declName prio => do
    let (leading, p) ← mkParserOfConstant s.categories declName
    Entry.parser catName declName leading p prio

builtin_initialize parserExtension : ParserExtension ←
  registerScopedEnvExtension {
    name            := `parserExt
    mkInitial       := ParserExtension.mkInitial
    addEntry        := ParserExtension.addEntryImpl
    toOLeanEntry    := ParserExtension.Entry.toOLeanEntry
    ofOLeanEntry    := ParserExtension.OLeanEntry.toEntry
  }

def isParserCategory (env : Environment) (catName : Name) : Bool :=
  (parserExtension.getState env).categories.contains catName

def addParserCategory (env : Environment) (catName : Name) (behavior : LeadingIdentBehavior) : Except String Environment := do
  if isParserCategory env catName then
    throwParserCategoryAlreadyDefined catName
  else
    return parserExtension.addEntry env <| ParserExtension.Entry.category catName behavior

def leadingIdentBehavior (env : Environment) (catName : Name) : LeadingIdentBehavior :=
  match getCategory (parserExtension.getState env).categories catName with
  | none     => LeadingIdentBehavior.default
  | some cat => cat.behavior

def mkCategoryAntiquotParser (kind : Name) : Parser :=
  mkAntiquot kind.toString none

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
  kinds.contains k

def getSyntaxNodeKinds (env : Environment) : List SyntaxNodeKind := do
  let kinds := (parserExtension.getState env).kinds
  kinds.foldl (fun ks k _ => k::ks) []

def getTokenTable (env : Environment) : TokenTable :=
  (parserExtension.getState env).tokens

def mkInputContext (input : String) (fileName : String) : InputContext := {
  input    := input,
  fileName := fileName,
  fileMap  := input.toFileMap
}

def mkParserContext (ictx : InputContext) (pmctx : ParserModuleContext) : ParserContext := {
  prec                  := 0,
  toInputContext        := ictx,
  toParserModuleContext := pmctx,
  tokens                := getTokenTable pmctx.env
}

def mkParserState (input : String) : ParserState :=
  { cache := initCacheForInput input }

/- convenience function for testing -/
def runParserCategory (env : Environment) (catName : Name) (input : String) (fileName := "<input>") : Except String Syntax :=
  let c := mkParserContext (mkInputContext input fileName) { env := env, options := {} }
  let s := mkParserState input
  let s := whitespace c s
  let s := categoryParserFnImpl catName c s
  if s.hasError then
    Except.error (s.toErrorMsg c)
  else if input.atEnd s.pos then
    Except.ok s.stxStack.back
  else
    Except.error ((s.mkError "end of input").toErrorMsg c)

def declareBuiltinParser (env : Environment) (addFnName : Name) (catName : Name) (declName : Name) (prio : Nat) : IO Environment :=
  let name := `_regBuiltinParser ++ declName
  let type := mkApp (mkConst `IO) (mkConst `Unit)
  let val  := mkAppN (mkConst addFnName) #[toExpr catName, toExpr declName, mkConst declName, mkRawNatLit prio]
  let decl := Declaration.defnDecl { name := name, levelParams := [], type := type, value := val, hints := ReducibilityHints.opaque,
                                     safety := DefinitionSafety.safe }
  match env.addAndCompile {} decl with
  -- TODO: pretty print error
  | Except.error _ => throw (IO.userError ("failed to emit registration code for builtin parser '" ++ toString declName ++ "'"))
  | Except.ok env  => IO.ofExcept (setBuiltinInitAttr env name)

def declareLeadingBuiltinParser (env : Environment) (catName : Name) (declName : Name) (prio : Nat) : IO Environment := -- TODO: use CoreM?
  declareBuiltinParser env `Lean.Parser.addBuiltinLeadingParser catName declName prio

def declareTrailingBuiltinParser (env : Environment) (catName : Name) (declName : Name) (prio : Nat) : IO Environment := -- TODO: use CoreM?
  declareBuiltinParser env `Lean.Parser.addBuiltinTrailingParser catName declName prio

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
  let env ← getEnv
  match decl.type with
  | Expr.const `Lean.Parser.TrailingParser _ _ => do
    let env ← declareTrailingBuiltinParser env catName declName prio
    setEnv env
  | Expr.const `Lean.Parser.Parser _ _ => do
    let env ← declareLeadingBuiltinParser env catName declName prio
    setEnv env
  | _ => throwError "unexpected parser type at '{declName}' (`Parser` or `TrailingParser` expected)"
  runParserAttributeHooks catName declName (builtin := true)

/-
The parsing tables for builtin parsers are "stored" in the extracted source code.
-/
def registerBuiltinParserAttribute (attrName : Name) (catName : Name) (behavior := LeadingIdentBehavior.default) : IO Unit := do
  addBuiltinParserCategory catName behavior
  registerBuiltinAttribute {
   name            := attrName,
   descr           := "Builtin parser",
   add             := fun declName stx kind => liftM $ BuiltinParserAttribute.add attrName catName declName stx kind,
   applicationTime := AttributeApplicationTime.afterCompilation
  }

private def ParserAttribute.add (attrName : Name) (catName : Name) (declName : Name) (stx : Syntax) (attrKind : AttributeKind) : AttrM Unit := do
  let prio ← Attribute.Builtin.getPrio stx
  let env ← getEnv
  let opts ← getOptions
  let categories := (parserExtension.getState env).categories
  let p ← mkParserOfConstant categories declName
  let leading    := p.1
  let parser     := p.2
  let tokens     := parser.info.collectTokens []
  tokens.forM fun token => do
    try
      addToken token attrKind
    catch
      | Exception.error ref msg => throwError "invalid parser '{declName}', {msg}"
      | ex => throw ex
  let kinds := parser.info.collectKinds {}
  kinds.forM fun kind _ => modifyEnv fun env => addSyntaxNodeKind env kind
  let entry := ParserExtension.Entry.parser catName declName leading parser prio
  match addParser categories catName declName leading parser prio with
  | Except.error ex => throwError ex
  | Except.ok _     => parserExtension.add entry attrKind
  runParserAttributeHooks catName declName (builtin := false)

def mkParserAttributeImpl (attrName : Name) (catName : Name) : AttributeImpl where
  name                      := attrName
  descr                     := "parser"
  add declName stx attrKind := ParserAttribute.add attrName catName declName stx attrKind
  applicationTime           := AttributeApplicationTime.afterCompilation

/- A builtin parser attribute that can be extended by users. -/
def registerBuiltinDynamicParserAttribute (attrName : Name) (catName : Name) : IO Unit := do
  registerBuiltinAttribute (mkParserAttributeImpl attrName catName)

builtin_initialize
  registerAttributeImplBuilder `parserAttr fun args =>
    match args with
    | [DataValue.ofName attrName, DataValue.ofName catName] => pure $ mkParserAttributeImpl attrName catName
    | _ => throw "invalid parser attribute implementation builder arguments"

def registerParserCategory (env : Environment) (attrName : Name) (catName : Name) (behavior := LeadingIdentBehavior.default) : IO Environment := do
  let env ← IO.ofExcept $ addParserCategory env catName behavior
  registerAttributeOfBuilder env `parserAttr [DataValue.ofName attrName, DataValue.ofName catName]

-- declare `termParser` here since it is used everywhere via antiquotations

builtin_initialize registerBuiltinParserAttribute `builtinTermParser `term

builtin_initialize registerBuiltinDynamicParserAttribute `termParser `term

-- declare `commandParser` to break cyclic dependency
builtin_initialize registerBuiltinParserAttribute `builtinCommandParser `command

builtin_initialize registerBuiltinDynamicParserAttribute `commandParser `command

@[inline] def commandParser (rbp : Nat := 0) : Parser :=
  categoryParser `command rbp

def notFollowedByCategoryTokenFn (catName : Name) : ParserFn := fun ctx s =>
  let categories := (parserExtension.getState ctx.env).categories
  match getCategory categories catName with
  | none => s.mkUnexpectedError s!"unknown parser category '{catName}'"
  | some cat =>
    let (s, stx) := peekToken ctx s
    match stx with
    | Except.ok (Syntax.atom _ sym) =>
      if ctx.quotDepth > 0 && sym == "$" then s
      else match cat.tables.leadingTable.find? (Name.mkSimple sym) with
      | some _ => s.mkUnexpectedError (toString catName)
      | _      => s
    | Except.ok _    => s
    | Except.error _ => s

@[inline] def notFollowedByCategoryToken (catName : Name) : Parser := {
  fn := notFollowedByCategoryTokenFn catName
}

abbrev notFollowedByCommandToken : Parser :=
  notFollowedByCategoryToken `command

abbrev notFollowedByTermToken : Parser :=
  notFollowedByCategoryToken `term

private def withNamespaces (ids : Array Name) (p : ParserFn) (addOpenSimple : Bool) : ParserFn := fun c s =>
  let c := ids.foldl (init := c) fun c id =>
    match ResolveName.resolveNamespace? c.env c.currNamespace c.openDecls id with
    | none => c -- Ignore namespace resolution errors, the elaborator will report them.
    | some ns =>
      let openDecls := if addOpenSimple then OpenDecl.simple ns [] :: c.openDecls else c.openDecls
      let env := parserExtension.activateScoped c.env ns
      { c with env, openDecls }
  let tokens := parserExtension.getState c.env |>.tokens
  p { c with tokens } s

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


@[inline] def withOpen (p : Parser) : Parser := {
  info := p.info
  fn   := withOpenFn  p.fn
}

/-- If the parsing stack is of the form `#[.., openDecl]`, we process the open declaration, and execute `p` -/
def withOpenDeclFn (p : ParserFn) : ParserFn := fun c s =>
  if s.stxStack.size > 0 then
    let stx := s.stxStack.back
    withOpenDeclFnCore stx p c s
  else
    p c s

@[inline] def withOpenDecl (p : Parser) : Parser := {
  info := p.info
  fn   := withOpenDeclFn  p.fn
}

end Parser
end Lean
