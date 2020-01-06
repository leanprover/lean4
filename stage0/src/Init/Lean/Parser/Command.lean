/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Parser.Term

namespace Lean
namespace Parser

@[init mkBuiltinParsingTablesRef]
constant builtinCommandParsingTable : IO.Ref ParsingTables := arbitrary _

@[init] def regBuiltinCommandParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinCommandParser `Lean.Parser.builtinCommandParsingTable

def mkCommandParserAttribute : IO ParserAttribute :=
registerParserAttribute `commandParser "command" "command parser" (some builtinCommandParsingTable)

@[init mkCommandParserAttribute]
constant commandParserAttribute : ParserAttribute := arbitrary _

@[inline] def commandParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
{ fn := fun _ => commandParserAttribute.runParserFn rbp }

/--
  Syntax quotation for terms and (lists of) commands. We prefer terms, so ambiguous quotations like
  `($x $y) will be parsed as an application, not two commands. Use `($x:command $y:command) instead.
  Multiple command will be put in a `null node, but a single command will not (so that you can directly
  match against a quotation in a command kind's elaborator). -/
@[builtinTermParser] def Term.stxQuot := parser! symbol "`(" appPrec >> (termParser <|> many1 commandParser true) >> ")"
@[builtinCommandParser] def Command.antiquot := (mkAntiquot "command" none true : Parser)

namespace Command
def commentBody : Parser :=
{ fn := rawFn (fun _ => finishCommentBlock 1) true }

def docComment       := parser! "/--" >> commentBody
def attrArg : Parser := ident <|> strLit <|> numLit
-- use `rawIdent` because of attribute names such as `instance`
def attrInstance     := parser! rawIdent >> many attrArg
def attributes       := parser! "@[" >> sepBy1 attrInstance ", " >> "]"
def «private»        := parser! "private "
def «protected»      := parser! "protected "
def visibility       := «private» <|> «protected»
def «noncomputable»  := parser! "noncomputable "
def «unsafe»         := parser! "unsafe "
def «partial»        := parser! "partial "
def declModifiers    := parser! optional docComment >> optional «attributes» >> optional visibility >> optional «noncomputable» >> optional «unsafe» >> optional «partial»
def declId           := parser! ident >> optional (".{" >> sepBy1 ident ", " >> "}")
def declSig          := parser! many Term.bracktedBinder >> Term.typeSpec
def optDeclSig       := parser! many Term.bracktedBinder >> Term.optType
def declValSimple    := parser! " := " >> termParser
def declValEqns      := parser! many1Indent Term.equation "equations must be indented"
def declVal          := declValSimple <|> declValEqns
def «abbrev»         := parser! "abbrev " >> declId >> optDeclSig >> declVal
def «def»            := parser! "def " >> declId >> optDeclSig >> declVal
def «theorem»        := parser! "theorem " >> declId >> declSig >> declVal
def «constant»       := parser! "constant " >> declId >> declSig >> optional declValSimple
def «instance»       := parser! "instance " >> optional declId >> declSig >> declVal
def «axiom»          := parser! "axiom " >> declId >> declSig
def «example»        := parser! "example " >> declSig >> declVal
def relaxedInferMod  := parser! try ("{" >> "}")
def strictInferMod   := parser! try ("(" >> ")")
def inferMod         := relaxedInferMod <|> strictInferMod
def introRule        := parser! " | " >> ident >> optional inferMod >> optDeclSig
def «inductive»      := parser! "inductive " >> declId >> optDeclSig >> many introRule
def classInductive   := parser! try ("class " >> "inductive ") >> declId >> optDeclSig >> many introRule
def structExplicitBinder := parser! "(" >> many ident >> optional inferMod >> optDeclSig >> optional Term.binderDefault >> ")"
def structImplicitBinder := parser! "{" >> many ident >> optional inferMod >> optDeclSig >> "}"
def structInstBinder     := parser! "[" >> many ident >> optional inferMod >> optDeclSig >> "]"
def structFields         := parser! many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
def structCtor           := parser! ident >> optional inferMod >> " :: "
def structureTk          := parser! "structure "
def classTk              := parser! "class "
def «extends»            := parser! " extends " >> sepBy1 termParser ", "
def «structure»          := parser! (structureTk <|> classTk) >> declId >> many Term.bracktedBinder >> optional «extends» >> Term.optType >> " := " >> optional structCtor >> structFields

@[builtinCommandParser] def declaration := parser!
declModifiers >> («abbrev» <|> «def» <|> «theorem» <|> «constant» <|> «instance» <|> «axiom» <|> «example» <|> «inductive» <|> classInductive <|> «structure»)

@[builtinCommandParser] def «section»      := parser! "section " >> optional ident
@[builtinCommandParser] def «namespace»    := parser! "namespace " >> ident
@[builtinCommandParser] def «end»          := parser! "end " >> optional ident
@[builtinCommandParser] def «variable»     := parser! "variable " >> Term.bracktedBinder
@[builtinCommandParser] def «variables»    := parser! "variables " >> many1 Term.bracktedBinder
@[builtinCommandParser] def «universe»     := parser! "universe " >> ident
@[builtinCommandParser] def «universes»    := parser! "universes " >> many1 ident
@[builtinCommandParser] def check          := parser! "#check " >> termParser
@[builtinCommandParser] def exit           := parser! "#exit"
@[builtinCommandParser] def «resolve_name» := parser! "#resolve_name " >> ident
@[builtinCommandParser] def «elab»         := parser! "#elab " >> termParser
@[builtinCommandParser] def «init_quot»    := parser! "init_quot"
@[builtinCommandParser] def «set_option»   := parser! "set_option " >> ident >> (symbolOrIdent "true" <|> symbolOrIdent "false" <|> strLit <|> numLit)
@[builtinCommandParser] def «attribute»    := parser! optional "local " >> "attribute " >> "[" >> sepBy1 attrInstance ", " >> "]" >> many1 ident
@[builtinCommandParser] def «export»       := parser! "export " >> ident >> "(" >> many1 ident >> ")"
def openHiding       := parser! try (ident >> "hiding") >> many1 ident
def openRenamingItem := parser! ident >> unicodeSymbol "→" "->" >> ident
def openRenaming     := parser! try (ident >> "renaming") >> sepBy1 openRenamingItem ", "
def openOnly         := parser! try (ident >> "(") >> many1 ident >> ")"
def openSimple       := parser! many1 ident
@[builtinCommandParser] def «open»       := parser! "open " >> (openHiding <|> openRenaming <|> openOnly <|> openSimple)

/- Lean3 command declaration commands -/
def maxPrec := parser! symbolOrIdent "max"
def precedenceLit : Parser := numLit <|> maxPrec
def «precedence» := parser! " : " >> precedenceLit
def quotedSymbolPrec := parser! quotedSymbol >> optional «precedence»
def symbol : Parser := quotedSymbolPrec <|> unquotedSymbol
def «prefix»   := parser! "prefix"
def «infix»    := parser! "infix"
def «infixl»   := parser! "infixl"
def «infixr»   := parser! "infixr"
def «postfix»  := parser! "postfix"
def mixfixKind := «prefix» <|> «infix» <|> «infixl» <|> «infixr» <|> «postfix»
@[builtinCommandParser] def «reserve»  := parser! "reserve " >> mixfixKind >> quotedSymbolPrec
def mixfixSymbol := quotedSymbolPrec <|> unquotedSymbol
@[builtinCommandParser] def «mixfix»   := parser! mixfixKind >> mixfixSymbol >> " := " >> termParser
def identPrec := parser! ident >> optional «precedence»
@[builtinCommandParser] def «notation» := parser! "notation" >> optional ident >> many (quotedSymbolPrec <|> identPrec) >> " := " >> termParser

end Command
end Parser
end Lean
