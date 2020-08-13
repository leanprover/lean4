/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/

/-! Extensible parsing via attributes -/

import Lean.Parser.Parser

namespace Lean
namespace Parser

def mkBuiltinTokenTable : IO (IO.Ref TokenTable) := IO.mkRef {}
@[init mkBuiltinTokenTable] constant builtinTokenTable : IO.Ref TokenTable := arbitrary _

/- Global table with all SyntaxNodeKind's -/
def mkBuiltinSyntaxNodeKindSetRef : IO (IO.Ref SyntaxNodeKindSet) := IO.mkRef {}
@[init mkBuiltinSyntaxNodeKindSetRef] constant builtinSyntaxNodeKindSetRef : IO.Ref SyntaxNodeKindSet := arbitrary _

def registerBuiltinNodeKind (k : SyntaxNodeKind) : IO Unit :=
builtinSyntaxNodeKindSetRef.modify fun s => s.insert k

@[init] private def registerAuxiliaryNodeKindSets : IO Unit := do
registerBuiltinNodeKind choiceKind;
registerBuiltinNodeKind identKind;
registerBuiltinNodeKind strLitKind;
registerBuiltinNodeKind numLitKind;
registerBuiltinNodeKind charLitKind;
registerBuiltinNodeKind nameLitKind;
pure ()

def mkBuiltinParserCategories : IO (IO.Ref ParserCategories) := IO.mkRef {}
@[init mkBuiltinParserCategories] constant builtinParserCategoriesRef : IO.Ref ParserCategories := arbitrary _

private def throwParserCategoryAlreadyDefined {α} (catName : Name) : ExceptT String Id α :=
throw ("parser category '" ++ toString catName ++ "' has already been defined")

private def addParserCategoryCore (categories : ParserCategories) (catName : Name) (initial : ParserCategory) : Except String ParserCategories :=
if categories.contains catName then
  throwParserCategoryAlreadyDefined catName
else
  pure $ categories.insert catName initial

/-- All builtin parser categories are Pratt's parsers -/
private def addBuiltinParserCategory (catName : Name) (leadingIdentAsSymbol : Bool) : IO Unit := do
categories ← builtinParserCategoriesRef.get;
categories ← IO.ofExcept $ addParserCategoryCore categories catName { tables := {}, leadingIdentAsSymbol := leadingIdentAsSymbol};
builtinParserCategoriesRef.set categories

inductive ParserExtensionOleanEntry
| token     (val : Token) : ParserExtensionOleanEntry
| kind      (val : SyntaxNodeKind) : ParserExtensionOleanEntry
| category  (catName : Name) (leadingIdentAsSymbol : Bool)
| parser    (catName : Name) (declName : Name) : ParserExtensionOleanEntry

inductive ParserExtensionEntry
| token     (val : Token) : ParserExtensionEntry
| kind      (val : SyntaxNodeKind) : ParserExtensionEntry
| category  (catName : Name) (leadingIdentAsSymbol : Bool)
| parser    (catName : Name) (declName : Name) (leading : Bool) (p : Parser) : ParserExtensionEntry

structure ParserExtensionState :=
(tokens      : TokenTable := {})
(kinds       : SyntaxNodeKindSet := {})
(categories  : ParserCategories := {})
(newEntries  : List ParserExtensionOleanEntry := [])

instance ParserExtensionState.inhabited : Inhabited ParserExtensionState := ⟨{}⟩

abbrev ParserExtension := PersistentEnvExtension ParserExtensionOleanEntry ParserExtensionEntry ParserExtensionState

private def ParserExtension.mkInitial : IO ParserExtensionState := do
tokens     ← builtinTokenTable.get;
kinds      ← builtinSyntaxNodeKindSetRef.get;
categories ← builtinParserCategoriesRef.get;
pure { tokens := tokens, kinds := kinds, categories := categories }

private def addTokenConfig (tokens : TokenTable) (tk : Token) : Except String TokenTable := do
if tk == "" then throw "invalid empty symbol"
else match tokens.find? tk with
  | none   => pure $ tokens.insert tk tk
  | some _ => pure tokens

def throwUnknownParserCategory {α} (catName : Name) : ExceptT String Id α :=
throw ("unknown parser category '" ++ toString catName ++ "'")

def addLeadingParser (categories : ParserCategories) (catName : Name) (parserName : Name) (p : Parser) : Except String ParserCategories :=
match categories.find? catName with
| none     =>
  throwUnknownParserCategory catName
| some cat =>
  let addTokens (tks : List Token) : Except String ParserCategories :=
    let tks    := tks.map $ fun tk => mkNameSimple tk;
    let tables := tks.eraseDups.foldl (fun (tables : PrattParsingTables) tk => { tables with leadingTable := tables.leadingTable.insert tk p }) cat.tables;
    pure $ categories.insert catName { cat with tables := tables };
  match p.info.firstTokens with
  | FirstTokens.tokens tks    => addTokens tks
  | FirstTokens.optTokens tks => addTokens tks
  | _ =>
    let tables := { cat.tables with leadingParsers := p :: cat.tables.leadingParsers };
    pure $ categories.insert catName { cat with tables := tables }

private def addTrailingParserAux (tables : PrattParsingTables) (p : TrailingParser) : PrattParsingTables :=
let addTokens (tks : List Token) : PrattParsingTables :=
  let tks := tks.map $ fun tk => mkNameSimple tk;
  tks.eraseDups.foldl (fun (tables : PrattParsingTables) tk => { tables with trailingTable := tables.trailingTable.insert tk p }) tables;
match p.info.firstTokens with
| FirstTokens.tokens tks    => addTokens tks
| FirstTokens.optTokens tks => addTokens tks
| _                         => { tables with trailingParsers := p :: tables.trailingParsers }

def addTrailingParser (categories : ParserCategories) (catName : Name) (p : TrailingParser) : Except String ParserCategories :=
match categories.find? catName with
| none     => throwUnknownParserCategory catName
| some cat => pure $ categories.insert catName { cat with tables := addTrailingParserAux cat.tables p }

def addParser (categories : ParserCategories) (catName : Name) (declName : Name) (leading : Bool) (p : Parser) : Except String ParserCategories :=
match leading, p with
| true, p  => addLeadingParser categories catName declName p
| false, p => addTrailingParser categories catName p

def addParserTokens (tokenTable : TokenTable) (info : ParserInfo) : Except String TokenTable :=
let newTokens := info.collectTokens [];
newTokens.foldlM addTokenConfig tokenTable

private def updateBuiltinTokens (info : ParserInfo) (declName : Name) : IO Unit := do
tokenTable ← builtinTokenTable.swap {};
match addParserTokens tokenTable info with
| Except.ok tokenTable => builtinTokenTable.set tokenTable
| Except.error msg     => throw (IO.userError ("invalid builtin parser '" ++ toString declName ++ "', " ++ msg))

def addBuiltinParser (catName : Name) (declName : Name) (leading : Bool) (p : Parser) : IO Unit := do
categories ← builtinParserCategoriesRef.get;
categories ← IO.ofExcept $ addParser categories catName declName leading p;
builtinParserCategoriesRef.set categories;
builtinSyntaxNodeKindSetRef.modify p.info.collectKinds;
updateBuiltinTokens p.info declName

def addBuiltinLeadingParser (catName : Name) (declName : Name) (p : Parser) : IO Unit :=
addBuiltinParser catName declName true p

def addBuiltinTrailingParser (catName : Name) (declName : Name) (p : TrailingParser) : IO Unit :=
addBuiltinParser catName declName false p

private def ParserExtension.addEntry (s : ParserExtensionState) (e : ParserExtensionEntry) : ParserExtensionState :=
match e with
| ParserExtensionEntry.token tk =>
  match addTokenConfig s.tokens tk with
  | Except.ok tokens => { s with tokens := tokens, newEntries := ParserExtensionOleanEntry.token tk :: s.newEntries }
  | _                => unreachable!
| ParserExtensionEntry.kind k =>
  { s with kinds := s.kinds.insert k, newEntries := ParserExtensionOleanEntry.kind k :: s.newEntries  }
| ParserExtensionEntry.category catName leadingIdentAsSymbol =>
  if s.categories.contains catName then s
  else { s with
         categories := s.categories.insert catName { tables := {}, leadingIdentAsSymbol := leadingIdentAsSymbol },
         newEntries := ParserExtensionOleanEntry.category catName leadingIdentAsSymbol :: s.newEntries }
| ParserExtensionEntry.parser catName declName leading parser =>
  match addParser s.categories catName declName leading parser with
  | Except.ok categories => { s with categories := categories, newEntries := ParserExtensionOleanEntry.parser catName declName :: s.newEntries }
  | _ => unreachable!

unsafe def mkParserOfConstantUnsafe
    (env : Environment) (categories : ParserCategories) (constName : Name)
    (compileParserDescr : ParserDescr → Except String Parser)
    : Except String (Bool × Parser) :=
match env.find? constName with
| none      => throw ("unknow constant '" ++ toString constName ++ "'")
| some info =>
  match info.type with
  | Expr.const `Lean.Parser.TrailingParser _ _ => do
    p ← env.evalConst Parser constName;
    pure ⟨false, p⟩
  | Expr.const `Lean.Parser.Parser _ _ => do
    p ← env.evalConst Parser constName;
    pure ⟨true, p⟩
  | Expr.const `Lean.ParserDescr _ _ => do
    d ← env.evalConst ParserDescr constName;
    p ← compileParserDescr d;
    pure ⟨true, p⟩
  | Expr.const `Lean.TrailingParserDescr _ _ => do
    d ← env.evalConst TrailingParserDescr constName;
    p ← compileParserDescr d;
    pure ⟨false, p⟩
  | _ => throw ("unexpected parser type at '" ++ toString constName ++ "' (`ParserDescr`, `TrailingParserDescr`, `Parser` or `TrailingParser` expected")

@[implementedBy mkParserOfConstantUnsafe]
constant mkParserOfConstantAux
    (env : Environment) (categories : ParserCategories) (constName : Name)
    (compileParserDescr : ParserDescr → Except String Parser)
    : Except String (Bool × Parser) :=
arbitrary _

partial def compileParserDescr (env : Environment) (categories : ParserCategories) : ParserDescr → Except String Parser
| ParserDescr.andthen d₁ d₂                       => andthen <$> compileParserDescr d₁ <*> compileParserDescr d₂
| ParserDescr.orelse d₁ d₂                        => orelse <$> compileParserDescr d₁ <*> compileParserDescr d₂
| ParserDescr.optional d                          => optional <$> compileParserDescr d
| ParserDescr.lookahead d                         => lookahead <$> compileParserDescr d
| ParserDescr.try d                               => try <$> compileParserDescr d
| ParserDescr.many d                              => many <$> compileParserDescr d
| ParserDescr.many1 d                             => many1 <$> compileParserDescr d
| ParserDescr.sepBy d₁ d₂                         => sepBy <$> compileParserDescr d₁ <*> compileParserDescr d₂
| ParserDescr.sepBy1 d₁ d₂                        => sepBy1 <$> compileParserDescr d₁ <*> compileParserDescr d₂
| ParserDescr.node k prec d                       => leadingNode k prec <$> compileParserDescr d
| ParserDescr.trailingNode k prec d               => trailingNode k prec <$> compileParserDescr d
| ParserDescr.symbol tk                           => pure $ symbol tk
| ParserDescr.numLit                              => pure $ numLit
| ParserDescr.strLit                              => pure $ strLit
| ParserDescr.charLit                             => pure $ charLit
| ParserDescr.nameLit                             => pure $ nameLit
| ParserDescr.ident                               => pure $ ident
| ParserDescr.nonReservedSymbol tk includeIdent   => pure $ nonReservedSymbol tk includeIdent
| ParserDescr.parser constName                    => do
  (_, p) ← mkParserOfConstantAux env categories constName compileParserDescr;
  pure p
| ParserDescr.cat catName prec                    =>
  match categories.find? catName with
  | some _ => pure $ categoryParser catName prec
  | none   => throwUnknownParserCategory catName

def mkParserOfConstant (env : Environment) (categories : ParserCategories) (constName : Name) : Except String (Bool × Parser) :=
mkParserOfConstantAux env categories constName (compileParserDescr env categories)

private def ParserExtension.addImported (env : Environment) (es : Array (Array ParserExtensionOleanEntry)) : IO ParserExtensionState := do
s ← ParserExtension.mkInitial;
es.foldlM
  (fun s entries =>
    entries.foldlM
      (fun s entry =>
       match entry with
       | ParserExtensionOleanEntry.token tk => do
         tokens ← IO.ofExcept (addTokenConfig s.tokens tk);
         pure { s with tokens := tokens }
       | ParserExtensionOleanEntry.kind k =>
         pure { s with kinds := s.kinds.insert k }
       | ParserExtensionOleanEntry.category catName leadingIdentAsSymbol => do
         categories ← IO.ofExcept (addParserCategoryCore s.categories catName { tables := {}, leadingIdentAsSymbol := leadingIdentAsSymbol});
         pure { s with categories := categories }
       | ParserExtensionOleanEntry.parser catName declName => do
         p ← IO.ofExcept $ mkParserOfConstant env s.categories declName;
         categories ← IO.ofExcept $ addParser s.categories catName declName p.1 p.2;
         -- discard result env; all imported parenthesizers should already be compiled
         _ ← PrettyPrinter.Parenthesizer.addParenthesizerFromConstant env declName;
         pure { s with categories := categories })
      s)
  s

def mkParserExtension : IO ParserExtension :=
registerPersistentEnvExtension {
  name            := `parserExt,
  mkInitial       := ParserExtension.mkInitial,
  addImportedFn   := ParserExtension.addImported,
  addEntryFn      := ParserExtension.addEntry,
  exportEntriesFn := fun s => s.newEntries.reverse.toArray,
  statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
}

@[init mkParserExtension]
constant parserExtension : ParserExtension := arbitrary _

def isParserCategory (env : Environment) (catName : Name) : Bool :=
(parserExtension.getState env).categories.contains catName

def addParserCategory (env : Environment) (catName : Name) (leadingIdentAsSymbol : Bool) : Except String Environment := do
if isParserCategory env catName then
  throwParserCategoryAlreadyDefined catName
else
  pure $ parserExtension.addEntry env $ ParserExtensionEntry.category catName leadingIdentAsSymbol

/-
  Return true if in the given category leading identifiers in parsers may be treated as atoms/symbols.
  See comment at `ParserCategory`. -/
def leadingIdentAsSymbol (env : Environment) (catName : Name) : Bool :=
match (parserExtension.getState env).categories.find? catName with
| none     => false
| some cat => cat.leadingIdentAsSymbol

def mkCategoryAntiquotParser (kind : Name) : Parser :=
mkAntiquot kind.toString none

def categoryParserFnImpl (catName : Name) : ParserFn :=
fun ctx s =>
  let categories := (parserExtension.getState ctx.env).categories;
  match categories.find? catName with
  | some cat =>
    prattParser catName cat.tables cat.leadingIdentAsSymbol (mkCategoryAntiquotParser catName).fn ctx s
  | none     => s.mkUnexpectedError ("unknown parser category '" ++ toString catName ++ "'")

@[init] def setCategoryParserFnRef : IO Unit :=
categoryParserFnRef.set categoryParserFnImpl

def addToken (env : Environment) (tk : Token) : Except String Environment := do
-- Recall that `ParserExtension.addEntry` is pure, and assumes `addTokenConfig` does not fail.
-- So, we must run it here to handle exception.
_ ← addTokenConfig (parserExtension.getState env).tokens tk;
pure $ parserExtension.addEntry env $ ParserExtensionEntry.token tk

def addSyntaxNodeKind (env : Environment) (k : SyntaxNodeKind) : Environment :=
parserExtension.addEntry env $ ParserExtensionEntry.kind k

def isValidSyntaxNodeKind (env : Environment) (k : SyntaxNodeKind) : Bool :=
let kinds := (parserExtension.getState env).kinds;
kinds.contains k

def getSyntaxNodeKinds (env : Environment) : List SyntaxNodeKind := do
let kinds := (parserExtension.getState env).kinds;
kinds.foldl (fun ks k _ => k::ks) []

def getTokenTable (env : Environment) : TokenTable :=
(parserExtension.getState env).tokens

def mkInputContext (input : String) (fileName : String) : InputContext :=
{ input    := input,
  fileName := fileName,
  fileMap  := input.toFileMap }

def mkParserContext (env : Environment) (ctx : InputContext) : ParserContext :=
{ prec           := 0,
  toInputContext := ctx,
  env            := env,
  tokens         := getTokenTable env }

def mkParserState (input : String) : ParserState :=
{ cache := initCacheForInput input }

/- convenience function for testing -/
def runParserCategory (env : Environment) (catName : Name) (input : String) (fileName := "<input>") : Except String Syntax :=
let c := mkParserContext env (mkInputContext input fileName);
let s := mkParserState input;
let s := whitespace c s;
let s := categoryParserFnImpl catName c s;
if s.hasError then
  Except.error (s.toErrorMsg c)
else
  Except.ok s.stxStack.back

def declareBuiltinParser (env : Environment) (addFnName : Name) (catName : Name) (declName : Name) : IO Environment :=
let name := `_regBuiltinParser ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
let val  := mkAppN (mkConst addFnName) #[toExpr catName, toExpr declName, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error _ => throw (IO.userError ("failed to emit registration code for builtin parser '" ++ toString declName ++ "'"))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

def declareLeadingBuiltinParser (env : Environment) (catName : Name) (declName : Name) : IO Environment :=
declareBuiltinParser env `Lean.Parser.addBuiltinLeadingParser catName declName

def declareTrailingBuiltinParser (env : Environment) (catName : Name) (declName : Name) : IO Environment :=
declareBuiltinParser env `Lean.Parser.addBuiltinTrailingParser catName declName

private def BuiltinParserAttribute.add (attrName : Name) (catName : Name)
    (env : Environment) (declName : Name) (args : Syntax) (persistent : Bool) : IO Environment := do
when args.hasArgs $ throw (IO.userError ("invalid attribute '" ++ toString attrName ++ "', unexpected argument"));
unless persistent $ throw (IO.userError ("invalid attribute '" ++ toString attrName ++ "', must be persistent"));
env ← match env.find? declName with
| none  => throw $ IO.userError "unknown declaration"
| some decl =>
  match decl.type with
 | Expr.const `Lean.Parser.TrailingParser _ _ =>
   declareTrailingBuiltinParser env catName declName
 | Expr.const `Lean.Parser.Parser _ _ =>
   declareLeadingBuiltinParser env catName declName
 | _ =>
   throw (IO.userError ("unexpected parser type at '" ++ toString declName ++ "' (`Parser` or `TrailingParser` expected"));
PrettyPrinter.Parenthesizer.compile env declName /- builtin -/ true

/-
The parsing tables for builtin parsers are "stored" in the extracted source code.
-/
def registerBuiltinParserAttribute (attrName : Name) (catName : Name) (leadingIdentAsSymbol := false) : IO Unit := do
addBuiltinParserCategory catName leadingIdentAsSymbol;
registerBuiltinAttribute {
 name            := attrName,
 descr           := "Builtin parser",
 add             := BuiltinParserAttribute.add attrName catName,
 applicationTime := AttributeApplicationTime.afterCompilation
}

private def ParserAttribute.add (attrName : Name) (catName : Name) (env : Environment) (declName : Name) (args : Syntax) (persistent : Bool) : IO Environment := do
when args.hasArgs $ throw (IO.userError ("invalid attribute '" ++ toString attrName ++ "', unexpected argument"));
let categories := (parserExtension.getState env).categories;
match mkParserOfConstant env categories declName with
| Except.error ex => throw (IO.userError ex)
| Except.ok p     => do
  let leading    := p.1;
  let parser     := p.2;
  let tokens     := parser.info.collectTokens [];
  env ← tokens.foldlM
    (fun env token =>
      match addToken env token with
      | Except.ok env    => pure env
      | Except.error msg => throw (IO.userError ("invalid parser '" ++ toString declName ++ "', " ++ msg)))
    env;
  let kinds := parser.info.collectKinds {};
  let env := kinds.foldl (fun env kind _ => addSyntaxNodeKind env kind) env;
  env ← match addParser categories catName declName leading parser with
  | Except.ok _     => pure $ parserExtension.addEntry env $ ParserExtensionEntry.parser catName declName leading parser
  | Except.error ex => throw (IO.userError ex);
  PrettyPrinter.Parenthesizer.addParenthesizerFromConstant env declName

def mkParserAttributeImpl (attrName : Name) (catName : Name) : AttributeImpl :=
{ name            := attrName,
  descr           := "parser",
  add             := ParserAttribute.add attrName catName,
  applicationTime := AttributeApplicationTime.afterCompilation }

/- A builtin parser attribute that can be extended by users. -/
def registerBuiltinDynamicParserAttribute (attrName : Name) (catName : Name) : IO Unit := do
registerBuiltinAttribute (mkParserAttributeImpl attrName catName)

@[init] private def registerParserAttributeImplBuilder : IO Unit :=
registerAttributeImplBuilder `parserAttr $ fun args =>
  match args with
  | [DataValue.ofName attrName, DataValue.ofName catName] => pure $ mkParserAttributeImpl attrName catName
  | _ => throw ("invalid parser attribute implementation builder arguments")

def registerParserCategory (env : Environment) (attrName : Name) (catName : Name) (leadingIdentAsSymbol := false) : IO Environment := do
env ← IO.ofExcept $ addParserCategory env catName leadingIdentAsSymbol;
registerAttributeOfBuilder env `parserAttr [DataValue.ofName attrName, DataValue.ofName catName]

-- declare `termParser` here since it is used everywhere via antiquotations

@[init] def regBuiltinTermParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinTermParser `term

@[init] def regTermParserAttribute : IO Unit :=
registerBuiltinDynamicParserAttribute `termParser `term

end Parser
end Lean
