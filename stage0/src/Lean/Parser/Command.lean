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
def commentBody : Parser :=
{ fn := rawFn (finishCommentBlock 1) true }

@[combinatorParenthesizer commentBody] def commentBody.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinatorFormatter commentBody] def commentBody.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

def docComment       := parser! ppDedent $ "/--" >> commentBody >> ppLine
def «private»        := parser! "private "
def «protected»      := parser! "protected "
def visibility       := «private» <|> «protected»
def «noncomputable»  := parser! "noncomputable "
def «unsafe»         := parser! "unsafe "
def «partial»        := parser! "partial "
def declModifiers (inline : Bool) := parser! optional docComment >> optional (Term.«attributes» >> if inline then skip else ppDedent ppLine) >> optional visibility >> optional «noncomputable» >> optional «unsafe» >> optional «partial»
def declId           := parser! ident >> optional (".{" >> sepBy1 ident ", " >> "}")
def declSig          := parser! ppGroup (many (ppSpace >> Term.bracketedBinder)) >> Term.typeSpec
def optDeclSig       := parser! ppGroup (many (ppSpace >> Term.bracketedBinder)) >> Term.optType
def declValSimple    := parser! ppDedent $ " :=\n" >> termParser
def declValEqns      := parser! Term.matchAlts false
def declVal          := declValSimple <|> declValEqns
def «abbrev»         := parser! "abbrev " >> declId >> optDeclSig >> declVal
def «def»            := parser! "def " >> declId >> optDeclSig >> declVal
def «theorem»        := parser! "theorem " >> declId >> declSig >> declVal
def «constant»       := parser! "constant " >> declId >> declSig >> optional declValSimple
def «instance»       := parser! "instance " >> optional declId >> declSig >> declVal
def «axiom»          := parser! "axiom " >> declId >> declSig
def «example»        := parser! "example " >> declSig >> declVal
def inferMod         := parser! try ("{" >> "}")
def ctor             := parser! "\n| " >> declModifiers true >> ident >> optional inferMod >> optDeclSig
def «inductive»      := parser! "inductive " >> declId >> optDeclSig >> ppDedent (many ctor)
def classInductive   := parser! try ("class " >> "inductive ") >> declId >> optDeclSig >> many ctor
def structExplicitBinder := parser! try (declModifiers true >> "(") >> many1 ident >> optional inferMod >> optDeclSig >> optional Term.binderDefault >> ")"
def structImplicitBinder := parser! try (declModifiers true >> "{") >> many1 ident >> optional inferMod >> declSig >> "}"
def structInstBinder     := parser! try (declModifiers true >> "[") >> many1 ident >> optional inferMod >> declSig >> "]"
def structFields         := parser! many (ppLine >> (structExplicitBinder <|> structImplicitBinder <|> structInstBinder))
def structCtor           := parser! try (declModifiers true >> ident >> optional inferMod >> " :: ")
def structureTk          := parser! "structure "
def classTk              := parser! "class "
def «extends»            := parser! " extends " >> sepBy1 termParser ", "
def «structure»          := parser! (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >> " := " >> optional structCtor >> ppDedent structFields
@[builtinCommandParser] def declaration := parser!
declModifiers false >> («abbrev» <|> «def» <|> «theorem» <|> «constant» <|> «instance» <|> «axiom» <|> «example» <|> «inductive» <|> classInductive <|> «structure»)

@[builtinCommandParser] def «section»      := parser! "section " >> optional ident
@[builtinCommandParser] def «namespace»    := parser! "namespace " >> ident
@[builtinCommandParser] def «end»          := parser! "end " >> optional ident
@[builtinCommandParser] def «variable»     := parser! "variable" >> Term.bracketedBinder
@[builtinCommandParser] def «variables»    := parser! "variables" >> many1 Term.bracketedBinder
@[builtinCommandParser] def «universe»     := parser! "universe " >> ident
@[builtinCommandParser] def «universes»    := parser! "universes " >> many1 ident
@[builtinCommandParser] def check          := parser! "#check " >> termParser
@[builtinCommandParser] def check_failure  := parser! "#check_failure " >> termParser -- Like `#check`, but succeeds only if term does not type check
@[builtinCommandParser] def eval           := parser! "#eval " >> termParser
@[builtinCommandParser] def synth          := parser! "#synth " >> termParser
@[builtinCommandParser] def exit           := parser! "#exit"
@[builtinCommandParser] def print          := parser! "#print " >> (ident <|> strLit)
@[builtinCommandParser] def printAxioms    := parser! "#print " >> "axioms " >> ident
@[builtinCommandParser] def «resolve_name» := parser! "#resolve_name " >> ident
@[builtinCommandParser] def «init_quot»    := parser! "init_quot"
@[builtinCommandParser] def «set_option»   := parser! "set_option " >> ident >> (nonReservedSymbol "true" <|> nonReservedSymbol "false" <|> strLit <|> numLit)
@[builtinCommandParser] def «attribute»    := parser! optional "local " >> "attribute " >> "[" >> sepBy1 Term.attrInstance ", " >> "] " >> many1 ident
@[builtinCommandParser] def «export»       := parser! "export " >> ident >> "(" >> many1 ident >> ")"
def openHiding       := parser! try (ident >> "hiding") >> many1 ident
def openRenamingItem := parser! ident >> unicodeSymbol "→" "->" >> ident
def openRenaming     := parser! try (ident >> "renaming") >> sepBy1 openRenamingItem ", "
def openOnly         := parser! try (ident >> "(") >> many1 ident >> ")"
def openSimple       := parser! many1 ident
@[builtinCommandParser] def «open»    := parser! "open " >> (openHiding <|> openRenaming <|> openOnly <|> openSimple)

@[builtinCommandParser] def «mutual» := parser! "mutual " >> many1 (notFollowedBy «end» >> commandParser) >> "end"
@[builtinCommandParser] def «initialize» := parser! "initialize " >> optional («try» (ident >> Term.typeSpec >> Term.leftArrow)) >> Term.doSeq

@[builtinCommandParser] def «in»  := tparser! " in " >> commandParser

end Command
end Parser
end Lean
