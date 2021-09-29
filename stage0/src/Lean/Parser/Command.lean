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
  `` `($x $y) `` will be parsed as an application, not two commands. Use `` `($x:command $y:command) `` instead.
  Multiple command will be put in a `` `null `` node, but a single command will not (so that you can directly
  match against a quotation in a command kind's elaborator). -/
-- TODO: use two separate quotation parsers with parser priorities instead
@[builtinTermParser] def Term.quot := leading_parser "`(" >> incQuotDepth (termParser <|> many1Unbox commandParser) >> ")"
@[builtinTermParser] def Term.precheckedQuot := leading_parser "`" >> Term.quot

namespace Command

-- A mutual block may be broken in different cliques, we identify them using an `ident` (an element of the clique)
def terminationByMany   := leading_parser atomic (lookahead (ident >> " => ")) >> many1Indent (group (ppLine >> ident >> " => " >> termParser >> optional ";"))
-- Simpler syntax for mutual blocks containing single clique that requires well-founded recursion.
def terminationBy1 := leading_parser termParser

def terminationBy := leading_parser "termination_by " >> (terminationByMany <|> terminationBy1)

@[builtinCommandParser]
def moduleDoc := leading_parser ppDedent $ "/-!" >> commentBody >> ppLine

def namedPrio := leading_parser (atomic ("(" >> nonReservedSymbol "priority") >> " := " >> priorityParser >> ")")
def optNamedPrio := optional namedPrio

def «private»        := leading_parser "private "
def «protected»      := leading_parser "protected "
def visibility       := «private» <|> «protected»
def «noncomputable»  := leading_parser "noncomputable "
def «unsafe»         := leading_parser "unsafe "
def «partial»        := leading_parser "partial "
def «nonrec»         := leading_parser "nonrec "
def declModifiers (inline : Bool) := leading_parser optional docComment >> optional (Term.«attributes» >> if inline then skip else ppDedent ppLine) >> optional visibility >> optional «noncomputable» >> optional «unsafe» >> optional («partial» <|> «nonrec»)
def declId           := leading_parser ident >> optional (".{" >> sepBy1 ident ", " >> "}")
def declSig          := leading_parser many (ppSpace >> (Term.simpleBinderWithoutType <|> Term.bracketedBinder)) >> Term.typeSpec
def optDeclSig       := leading_parser many (ppSpace >> (Term.simpleBinderWithoutType <|> Term.bracketedBinder)) >> Term.optType
def declValSimple    := leading_parser " :=\n" >> termParser >> optional Term.whereDecls
def declValEqns      := leading_parser Term.matchAltsWhereDecls
def declVal          := declValSimple <|> declValEqns <|> Term.whereDecls
def «abbrev»         := leading_parser "abbrev " >> declId >> optDeclSig >> declVal
def optDefDeriving   := optional (atomic ("deriving " >> notSymbol "instance") >> sepBy1 ident ", ")
def «def»            := leading_parser "def " >> declId >> optDeclSig >> declVal >> optDefDeriving >> optional terminationBy
def «theorem»        := leading_parser "theorem " >> declId >> declSig >> declVal >> optional terminationBy
def «constant»       := leading_parser "constant " >> declId >> declSig >> optional declValSimple
def «instance»       := leading_parser Term.attrKind >> "instance " >> optNamedPrio >> optional declId >> declSig >> declVal >> optional terminationBy
def «axiom»          := leading_parser "axiom " >> declId >> declSig
def «example»        := leading_parser "example " >> declSig >> declVal
def inferMod         := leading_parser atomic (symbol "{" >> "}")
def ctor             := leading_parser "\n| " >> declModifiers true >> ident >> optional inferMod >> optDeclSig
def derivingClasses  := sepBy1 (group (ident >> optional (" with " >> Term.structInst))) ", "
def optDeriving      := leading_parser optional (atomic ("deriving " >> notSymbol "instance") >> derivingClasses)
def «inductive»      := leading_parser "inductive " >> declId >> optDeclSig >> optional (symbol ":=" <|> "where") >> many ctor >> optDeriving
def classInductive   := leading_parser atomic (group (symbol "class " >> "inductive ")) >> declId >> optDeclSig >> optional (symbol ":=" <|> "where") >> many ctor >> optDeriving
def structExplicitBinder := leading_parser atomic (declModifiers true >> "(") >> many1 ident >> optional inferMod >> optDeclSig >> optional (Term.binderTactic <|> Term.binderDefault) >> ")"
def structImplicitBinder := leading_parser atomic (declModifiers true >> "{") >> many1 ident >> optional inferMod >> declSig >> "}"
def structInstBinder     := leading_parser atomic (declModifiers true >> "[") >> many1 ident >> optional inferMod >> declSig >> "]"
def structSimpleBinder   := leading_parser atomic (declModifiers true >> ident) >> optional inferMod >> optDeclSig >> optional (Term.binderTactic <|> Term.binderDefault)
def structFields         := leading_parser manyIndent (ppLine >> checkColGe >>(structExplicitBinder <|> structImplicitBinder <|> structInstBinder <|> structSimpleBinder))
def structCtor           := leading_parser atomic (declModifiers true >> ident >> optional inferMod >> " :: ")
def structureTk          := leading_parser "structure "
def classTk              := leading_parser "class "
def «extends»            := leading_parser " extends " >> sepBy1 termParser ", "
def «structure»          := leading_parser
    (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType
    >> optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields)
    >> optDeriving
@[builtinCommandParser] def declaration := leading_parser
declModifiers false >> («abbrev» <|> «def» <|> «theorem» <|> «constant» <|> «instance» <|> «axiom» <|> «example» <|> «inductive» <|> classInductive <|> «structure»)
@[builtinCommandParser] def «deriving»     := leading_parser "deriving " >> "instance " >> derivingClasses >> " for " >> sepBy1 ident ", "
@[builtinCommandParser] def «section»      := leading_parser "section " >> optional ident
@[builtinCommandParser] def «namespace»    := leading_parser "namespace " >> ident
@[builtinCommandParser] def «end»          := leading_parser "end " >> optional ident
@[builtinCommandParser] def «variable»     := leading_parser "variable" >> many1 Term.bracketedBinder
@[builtinCommandParser] def «universe»     := leading_parser "universe " >> many1 ident
@[builtinCommandParser] def check          := leading_parser "#check " >> termParser
@[builtinCommandParser] def check_failure  := leading_parser "#check_failure " >> termParser -- Like `#check`, but succeeds only if term does not type check
@[builtinCommandParser] def reduce         := leading_parser "#reduce " >> termParser
@[builtinCommandParser] def eval           := leading_parser "#eval " >> termParser
@[builtinCommandParser] def synth          := leading_parser "#synth " >> termParser
@[builtinCommandParser] def exit           := leading_parser "#exit"
@[builtinCommandParser] def print          := leading_parser "#print " >> (ident <|> strLit)
@[builtinCommandParser] def printAxioms    := leading_parser "#print " >> nonReservedSymbol "axioms " >> ident
@[builtinCommandParser] def «resolve_name» := leading_parser "#resolve_name " >> ident
@[builtinCommandParser] def «init_quot»    := leading_parser "init_quot"
def optionValue := nonReservedSymbol "true" <|> nonReservedSymbol "false" <|> strLit <|> numLit
@[builtinCommandParser] def «set_option»   := leading_parser "set_option " >> ident >> ppSpace >> optionValue
def eraseAttr := leading_parser "-" >> rawIdent
@[builtinCommandParser] def «attribute»    := leading_parser "attribute " >> "[" >> sepBy1 (eraseAttr <|> Term.attrInstance) ", " >> "] " >> many1 ident
@[builtinCommandParser] def «export»       := leading_parser "export " >> ident >> "(" >> many1 ident >> ")"
def openHiding       := leading_parser atomic (ident >> "hiding") >> many1 (checkColGt >> ident)
def openRenamingItem := leading_parser ident >> unicodeSymbol "→" "->" >> checkColGt >> ident
def openRenaming     := leading_parser atomic (ident >> "renaming") >> sepBy1 openRenamingItem ", "
def openOnly         := leading_parser atomic (ident >> "(") >> many1 ident >> ")"
def openSimple       := leading_parser many1 (checkColGt >> ident)
def openScoped       := leading_parser "scoped " >> many1 (checkColGt >> ident)
def openDecl         := openHiding <|> openRenaming <|> openOnly <|> openSimple <|> openScoped
@[builtinCommandParser] def «open»    := leading_parser withPosition ("open " >> openDecl)

@[builtinCommandParser] def «mutual» := leading_parser "mutual " >> many1 (ppLine >> notSymbol "end" >> commandParser) >> ppDedent (ppLine >> "end") >> optional terminationBy
@[builtinCommandParser] def «initialize» := leading_parser optional visibility >> "initialize " >> optional (atomic (ident >> Term.typeSpec >> Term.leftArrow)) >> Term.doSeq
@[builtinCommandParser] def «builtin_initialize» := leading_parser optional visibility >> "builtin_initialize " >> optional (atomic (ident >> Term.typeSpec >> Term.leftArrow)) >> Term.doSeq

@[builtinCommandParser] def «in»  := trailing_parser withOpen (" in " >> commandParser)

/-
  This is an auxiliary command for generation constructor injectivity theorems for inductive types defined at `Prelude.lean`.
  It is meant for bootstrapping purposes only. -/
@[builtinCommandParser] def genInjectiveTheorems := leading_parser "gen_injective_theorems% " >> ident

@[runBuiltinParserAttributeHooks] abbrev declModifiersF := declModifiers false
@[runBuiltinParserAttributeHooks] abbrev declModifiersT := declModifiers true

builtin_initialize
  register_parser_alias "declModifiers"       declModifiersF
  register_parser_alias "nestedDeclModifiers" declModifiersT
  register_parser_alias                       declId
  register_parser_alias                       declSig
  register_parser_alias                       declVal
  register_parser_alias                       optDeclSig
  register_parser_alias                       openDecl

end Command

namespace Term
@[builtinTermParser] def «open» := leading_parser:leadPrec "open " >> Command.openDecl >> withOpenDecl (" in " >> termParser)
@[builtinTermParser] def «set_option» := leading_parser:leadPrec "set_option " >> ident >> ppSpace >> Command.optionValue >> " in " >> termParser
end Term

namespace Tactic
@[builtinTacticParser] def «open» := leading_parser:leadPrec "open " >> Command.openDecl >> withOpenDecl (" in " >> tacticSeq)
@[builtinTacticParser] def «set_option» := leading_parser:leadPrec "set_option " >> ident >> ppSpace >> Command.optionValue >> " in " >> tacticSeq
end Tactic

end Parser
end Lean
