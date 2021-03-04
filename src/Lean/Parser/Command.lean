/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Term
import Lean.Parser.Do

namespace Lean
namespace Parser

/--
  Syntax quotation for terms and (lists of) commands. We prefer terms, so ambiguous quotations like
  `($x $y) will be parsed as an application, not two commands. Use `($x:command $y:command) instead.
  Multiple command will be put in a `null node, but a single command will not (so that you can directly
  match against a quotation in a command kind's elaborator). -/
-- TODO: use two separate quotation parsers with parser priorities instead
@[builtinTermParser] def Term.quot := parser! "`(" >> toggleInsideQuot (termParser <|> many1Unbox commandParser) >> ")"

namespace Command

def namedPrio := parser! (atomic ("(" >> nonReservedSymbol "priority") >> " := " >> priorityParser >> ")")
def optNamedPrio := optional namedPrio

def «private»        := parser! "private "
def «protected»      := parser! "protected "
def visibility       := «private» <|> «protected»
def «noncomputable»  := parser! "noncomputable "
def «unsafe»         := parser! "unsafe "
def «partial»        := parser! "partial "
def declModifiers (inline : Bool) := parser! optional docComment >> optional (Term.«attributes» >> if inline then skip else ppDedent ppLine) >> optional visibility >> optional «noncomputable» >> optional «unsafe» >> optional «partial»
def declId           := parser! ident >> optional (".{" >> sepBy1 ident ", " >> "}")
def declSig          := parser! many (ppSpace >> (Term.simpleBinderWithoutType <|> Term.bracketedBinder)) >> Term.typeSpec
def optDeclSig       := parser! many (ppSpace >> (Term.simpleBinderWithoutType <|> Term.bracketedBinder)) >> Term.optType
def declValSimple    := parser! " :=\n" >> termParser >> optional Term.whereDecls
def declValEqns      := parser! Term.matchAltsWhereDecls
def declVal          := declValSimple <|> declValEqns <|> Term.whereDecls
def «abbrev»         := parser! "abbrev " >> declId >> optDeclSig >> declVal
def «def»            := parser! "def " >> declId >> optDeclSig >> declVal
def «theorem»        := parser! "theorem " >> declId >> declSig >> declVal
def «constant»       := parser! "constant " >> declId >> declSig >> optional declValSimple
def «instance»       := parser! Term.attrKind >> "instance " >> optNamedPrio >> optional declId >> declSig >> declVal
def «axiom»          := parser! "axiom " >> declId >> declSig
def «example»        := parser! "example " >> declSig >> declVal
def inferMod         := parser! atomic (symbol "{" >> "}")
def ctor             := parser! "\n| " >> declModifiers true >> ident >> optional inferMod >> optDeclSig
def optDeriving      := parser! optional (atomic ("deriving " >> notSymbol "instance") >> sepBy1 ident ", ")
def «inductive»      := parser! "inductive " >> declId >> optDeclSig >> optional (symbol ":=" <|> "where") >> many ctor >> optDeriving
def classInductive   := parser! atomic (group (symbol "class " >> "inductive ")) >> declId >> optDeclSig >> optional (symbol ":=" <|> "where") >> many ctor >> optDeriving
def structExplicitBinder := parser! atomic (declModifiers true >> "(") >> many1 ident >> optional inferMod >> optDeclSig >> optional Term.binderDefault >> ")"
def structImplicitBinder := parser! atomic (declModifiers true >> "{") >> many1 ident >> optional inferMod >> declSig >> "}"
def structInstBinder     := parser! atomic (declModifiers true >> "[") >> many1 ident >> optional inferMod >> declSig >> "]"
def structSimpleBinder   := parser! atomic (declModifiers true >> ident) >> optional inferMod >> optDeclSig >> optional Term.binderDefault
def structFields         := parser! manyIndent (ppLine >> checkColGe >>(structExplicitBinder <|> structImplicitBinder <|> structInstBinder <|> structSimpleBinder))
def structCtor           := parser! atomic (declModifiers true >> ident >> optional inferMod >> " :: ")
def structureTk          := parser! "structure "
def classTk              := parser! "class "
def «extends»            := parser! " extends " >> sepBy1 termParser ", "
def «structure»          := parser!
    (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType
    >> optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields)
    >> optDeriving
@[builtinCommandParser] def declaration := parser!
declModifiers false >> («abbrev» <|> «def» <|> «theorem» <|> «constant» <|> «instance» <|> «axiom» <|> «example» <|> «inductive» <|> classInductive <|> «structure»)
@[builtinCommandParser] def «deriving»     := parser! "deriving " >> "instance " >> sepBy1 ident ", " >> " for " >> sepBy1 ident ", "
@[builtinCommandParser] def «section»      := parser! "section " >> optional ident
@[builtinCommandParser] def «namespace»    := parser! "namespace " >> ident
@[builtinCommandParser] def «end»          := parser! "end " >> optional ident
@[builtinCommandParser] def «variable»     := parser! "variable" >> many1 Term.bracketedBinder
@[builtinCommandParser] def «universe»     := parser! "universe " >> ident
@[builtinCommandParser] def «universes»    := parser! "universes " >> many1 ident
@[builtinCommandParser] def check          := parser! "#check " >> termParser
@[builtinCommandParser] def check_failure  := parser! "#check_failure " >> termParser -- Like `#check`, but succeeds only if term does not type check
@[builtinCommandParser] def reduce         := parser! "#reduce " >> termParser
@[builtinCommandParser] def eval           := parser! "#eval " >> termParser
@[builtinCommandParser] def synth          := parser! "#synth " >> termParser
@[builtinCommandParser] def exit           := parser! "#exit"
@[builtinCommandParser] def print          := parser! "#print " >> (ident <|> strLit)
@[builtinCommandParser] def printAxioms    := parser! "#print " >> nonReservedSymbol "axioms " >> ident
@[builtinCommandParser] def «resolve_name» := parser! "#resolve_name " >> ident
@[builtinCommandParser] def «init_quot»    := parser! "init_quot"
@[builtinCommandParser] def «set_option»   := parser! "set_option " >> ident >> ppSpace >> (nonReservedSymbol "true" <|> nonReservedSymbol "false" <|> strLit <|> numLit)
def eraseAttr := parser! "-" >> ident 
@[builtinCommandParser] def «attribute»    := parser! "attribute " >> "[" >> sepBy1 (eraseAttr <|> Term.attrInstance) ", " >> "] " >> many1 ident
@[builtinCommandParser] def «export»       := parser! "export " >> ident >> "(" >> many1 ident >> ")"
def openHiding       := parser! atomic (ident >> "hiding") >> many1 ident
def openRenamingItem := parser! ident >> unicodeSymbol "→" "->" >> ident
def openRenaming     := parser! atomic (ident >> "renaming") >> sepBy1 openRenamingItem ", "
def openOnly         := parser! atomic (ident >> "(") >> many1 ident >> ")"
def openSimple       := parser! many1 ident
@[builtinCommandParser] def «open»    := parser! "open " >> (openHiding <|> openRenaming <|> openOnly <|> openSimple)

@[builtinCommandParser] def «mutual» := parser! "mutual " >> many1 (ppLine >> notSymbol "end" >> commandParser) >> ppDedent (ppLine >> "end")
@[builtinCommandParser] def «initialize» := parser! "initialize " >> optional (atomic (ident >> Term.typeSpec >> Term.leftArrow)) >> Term.doSeq
@[builtinCommandParser] def «builtin_initialize» := parser! "builtin_initialize " >> optional (atomic (ident >> Term.typeSpec >> Term.leftArrow)) >> Term.doSeq

@[builtinCommandParser] def «in»  := tparser! " in " >> commandParser

@[runBuiltinParserAttributeHooks] abbrev declModifiersF := declModifiers false
@[runBuiltinParserAttributeHooks] abbrev declModifiersT := declModifiers true

builtin_initialize
  registerParserAlias! "declModifiers"       declModifiersF
  registerParserAlias! "nestedDeclModifiers" declModifiersT
  registerParserAlias! "declId"              declId
  registerParserAlias! "declSig"             declSig
  registerParserAlias! "optDeclSig"          optDeclSig

end Command
end Parser
end Lean
