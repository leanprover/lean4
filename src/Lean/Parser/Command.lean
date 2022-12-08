/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Term
import Lean.Parser.Do

namespace Lean
namespace Parser

/-- Syntax quotation for terms. -/
@[builtin_term_parser] def Term.quot := leading_parser
  "`(" >> withoutPosition (incQuotDepth termParser) >> ")"
@[builtin_term_parser] def Term.precheckedQuot := leading_parser
  "`" >> Term.quot

namespace Command

/--
Syntax quotation for (sequences of) commands.
The identical syntax for term quotations takes priority,
so ambiguous quotations like `` `($x $y) `` will be parsed as an application,
not two commands. Use `` `($x:command $y:command) `` instead.
Multiple commands will be put in a `` `null `` node,
but a single command will not (so that you can directly
match against a quotation in a command kind's elaborator). -/
@[builtin_term_parser low] def quot := leading_parser
  "`(" >> withoutPosition (incQuotDepth (many1Unbox commandParser)) >> ")"

/-
A mutual block may be broken in different cliques,
we identify them using an `ident` (an element of the clique).
We provide two kinds of hints to the termination checker:
1- A wellfounded relation (`p` is `termParser`)
2- A tactic for proving the recursive applications are "decreasing" (`p` is `tacticSeq`)
-/
def terminationHintMany (p : Parser) := leading_parser
  atomic (lookahead (ident >> " => ")) >>
  many1Indent (group (ppLine >> ident >> " => " >> p >> optional ";"))
def terminationHint1 (p : Parser) := leading_parser p
def terminationHint (p : Parser) := terminationHintMany p <|> terminationHint1 p

def terminationByCore := leading_parser
  "termination_by' " >> terminationHint termParser
def decreasingBy := leading_parser
  "decreasing_by " >> terminationHint Tactic.tacticSeq

def terminationByElement   := leading_parser
  ppLine >> (ident <|> Term.hole) >> many (ident <|> Term.hole) >>
  " => " >> termParser >> optional ";"
def terminationBy          := leading_parser
  ppLine >> "termination_by " >> many1Indent terminationByElement

def terminationSuffix :=
  optional (terminationBy <|> terminationByCore) >> optional decreasingBy

@[builtin_command_parser]
def moduleDoc := leading_parser ppDedent <|
  "/-!" >> commentBody >> ppLine

def namedPrio := leading_parser
  atomic ("(" >> nonReservedSymbol "priority") >> " := " >> withoutPosition priorityParser >> ")"
def optNamedPrio := optional (ppSpace >> namedPrio)

def «private»        := leading_parser "private "
def «protected»      := leading_parser "protected "
def visibility       := «private» <|> «protected»
def «noncomputable»  := leading_parser "noncomputable "
def «unsafe»         := leading_parser "unsafe "
def «partial»        := leading_parser "partial "
def «nonrec»         := leading_parser "nonrec "
def declModifiers (inline : Bool) := leading_parser
  optional docComment >>
  optional (Term.«attributes» >> if inline then skip else ppDedent ppLine) >>
  optional visibility >>
  optional «noncomputable» >>
  optional «unsafe» >>
  optional («partial» <|> «nonrec»)
def declId           := leading_parser
  ident >> optional (".{" >> sepBy1 ident ", " >> "}")
def declSig          := leading_parser
  many (ppSpace >> (Term.binderIdent <|> Term.bracketedBinder)) >> Term.typeSpec
def optDeclSig       := leading_parser
  many (ppSpace >> (Term.binderIdent <|> Term.bracketedBinder)) >> Term.optType
def declValSimple    := leading_parser
  " :=" >> ppHardLineUnlessUngrouped >> termParser >> optional Term.whereDecls
def declValEqns      := leading_parser
  Term.matchAltsWhereDecls
def whereStructField := leading_parser
  Term.letDecl
def whereStructInst  := leading_parser
  " where" >> sepByIndent (ppGroup whereStructField) "; " (allowTrailingSep := true) >>
  optional Term.whereDecls
/-
  Remark: we should not use `Term.whereDecls` at `declVal`
  because `Term.whereDecls` is defined using `Term.letRecDecl` which may contain attributes.
  Issue #753 showns an example that fails to be parsed when we used `Term.whereDecls`.
-/
def declVal          :=
  withAntiquot (mkAntiquot "declVal" `Lean.Parser.Command.declVal (isPseudoKind := true)) <|
    declValSimple <|> declValEqns <|> whereStructInst
def «abbrev»         := leading_parser
  "abbrev " >> declId >> ppIndent optDeclSig >> declVal >> terminationSuffix
def optDefDeriving   :=
  optional (atomic ("deriving " >> notSymbol "instance") >> sepBy1 ident ", ")
def «def»            := leading_parser
  "def " >> declId >> ppIndent optDeclSig >> declVal >> optDefDeriving >> terminationSuffix
def «theorem»        := leading_parser
  "theorem " >> declId >> ppIndent declSig >> declVal >> terminationSuffix
def «opaque»         := leading_parser
  "opaque " >> declId >> ppIndent declSig >> optional declValSimple
/- As `declSig` starts with a space, "instance" does not need a trailing space
  if we put `ppSpace` in the optional fragments. -/
def «instance»       := leading_parser
  Term.attrKind >> "instance" >> optNamedPrio >>
  optional (ppSpace >> declId) >> ppIndent declSig >> declVal >> terminationSuffix
def «axiom»          := leading_parser
  "axiom " >> declId >> ppIndent declSig
/- As `declSig` starts with a space, "example" does not need a trailing space. -/
def «example»        := leading_parser
  "example" >> ppIndent optDeclSig >> declVal
def ctor             := leading_parser
  atomic (optional docComment >> "\n| ") >>
  ppGroup (declModifiers true >> rawIdent >> optDeclSig)
def derivingClasses  := sepBy1 (group (ident >> optional (" with " >> Term.structInst))) ", "
def optDeriving      := leading_parser
  optional (ppLine >> atomic ("deriving " >> notSymbol "instance") >> derivingClasses)
def computedField    := leading_parser
  declModifiers true >> ident >> " : " >> termParser >> Term.matchAlts
def computedFields   := leading_parser
  "with" >> manyIndent (ppLine >> ppGroup computedField)
/--
In Lean, every concrete type other than the universes
and every type constructor other than dependent arrows
is an instance of a general family of type constructions known as inductive types.
It is remarkable that it is possible to construct a substantial edifice of mathematics
based on nothing more than the type universes, dependent arrow types, and inductive types;
everything else follows from those.
Intuitively, an inductive type is built up from a specified list of constructor.
For example, `List α` is the list of elements of type `α`, and is defined as follows:
```
inductive List (α : Type u) where
| nil
| cons (head : α) (tail : List α)
```
A list of elements of type `α` is either the empty list, `nil`,
or an element `head : α` followed by a list `tail : List α`.
For more information about [inductive types](https://leanprover.github.io/theorem_proving_in_lean4/inductive_types.html).
-/
def «inductive»      := leading_parser
  "inductive " >> declId >> optDeclSig >> optional (symbol " :=" <|> " where") >>
  many ctor >> optional (ppDedent ppLine >> computedFields) >> optDeriving
def classInductive   := leading_parser
  atomic (group (symbol "class " >> "inductive ")) >>
  declId >> ppIndent optDeclSig >>
  optional (symbol " :=" <|> " where") >> many ctor >> optDeriving
def structExplicitBinder := leading_parser
  atomic (declModifiers true >> "(") >>
  withoutPosition (many1 ident >> ppIndent optDeclSig >>
    optional (Term.binderTactic <|> Term.binderDefault)) >> ")"
def structImplicitBinder := leading_parser
  atomic (declModifiers true >> "{") >> withoutPosition (many1 ident >> declSig) >> "}"
def structInstBinder     := leading_parser
  atomic (declModifiers true >> "[") >> withoutPosition (many1 ident >> declSig) >> "]"
def structSimpleBinder   := leading_parser
  atomic (declModifiers true >> ident) >> optDeclSig >>
  optional (Term.binderTactic <|> Term.binderDefault)
def structFields         := leading_parser
  manyIndent <|
    ppLine >> checkColGe >> ppGroup (
      structExplicitBinder <|> structImplicitBinder <|>
      structInstBinder <|> structSimpleBinder)
def structCtor           := leading_parser
  atomic (declModifiers true >> ident >> " :: ")
def structureTk          := leading_parser
  "structure "
def classTk              := leading_parser
  "class "
def «extends»            := leading_parser
  " extends " >> sepBy1 termParser ", "
def «structure»          := leading_parser
    (structureTk <|> classTk) >>
    declId >> many (ppSpace >> Term.bracketedBinder) >>
    optional «extends» >> Term.optType >>
    optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields) >>
    optDeriving
@[builtin_command_parser] def declaration := leading_parser
  declModifiers false >>
  («abbrev» <|> «def» <|> «theorem» <|> «opaque» <|> «instance» <|> «axiom» <|> «example» <|>
   «inductive» <|> classInductive <|> «structure»)
@[builtin_command_parser] def «deriving»     := leading_parser
  "deriving " >> "instance " >> derivingClasses >> " for " >> sepBy1 ident ", "
@[builtin_command_parser] def noncomputableSection := leading_parser
  "noncomputable " >> "section " >> optional ident
@[builtin_command_parser] def «section»      := leading_parser
  "section " >> optional ident
@[builtin_command_parser] def «namespace»    := leading_parser
  "namespace " >> ident
@[builtin_command_parser] def «end»          := leading_parser
  "end " >> optional ident
@[builtin_command_parser] def «variable»     := leading_parser
  "variable" >> many1 (ppSpace >> Term.bracketedBinder)
@[builtin_command_parser] def «universe»     := leading_parser
  "universe " >> many1 ident
@[builtin_command_parser] def check          := leading_parser
  "#check " >> termParser
@[builtin_command_parser] def check_failure  := leading_parser
  "#check_failure " >> termParser -- Like `#check`, but succeeds only if term does not type check
@[builtin_command_parser] def reduce         := leading_parser
  "#reduce " >> termParser
@[builtin_command_parser] def eval           := leading_parser
  "#eval " >> termParser
@[builtin_command_parser] def synth          := leading_parser
  "#synth " >> termParser
@[builtin_command_parser] def exit           := leading_parser
  "#exit"
@[builtin_command_parser] def print          := leading_parser
  "#print " >> (ident <|> strLit)
@[builtin_command_parser] def printAxioms    := leading_parser
  "#print " >> nonReservedSymbol "axioms " >> ident
@[builtin_command_parser] def «init_quot»    := leading_parser
  "init_quot"
def optionValue := nonReservedSymbol "true" <|> nonReservedSymbol "false" <|> strLit <|> numLit
@[builtin_command_parser] def «set_option»   := leading_parser
  "set_option " >> ident >> ppSpace >> optionValue
def eraseAttr := leading_parser
  "-" >> rawIdent
@[builtin_command_parser] def «attribute»    := leading_parser
  "attribute " >> "[" >>
    withoutPosition (sepBy1 (eraseAttr <|> Term.attrInstance) ", ") >>
  "] " >> many1 ident
@[builtin_command_parser] def «export»       := leading_parser
  "export " >> ident >> " (" >> many1 ident >> ")"
@[builtin_command_parser] def «import»       := leading_parser
  "import" -- not a real command, only for error messages
def openHiding       := leading_parser
  atomic (ident >> "hiding") >> many1 (checkColGt >> ident)
def openRenamingItem := leading_parser
  ident >> unicodeSymbol " → " " -> " >> checkColGt >> ident
def openRenaming     := leading_parser
  atomic (ident >> "renaming") >> sepBy1 openRenamingItem ", "
def openOnly         := leading_parser
  atomic (ident >> " (") >> many1 ident >> ")"
def openSimple       := leading_parser
  many1 (checkColGt >> ident)
def openScoped       := leading_parser
  "scoped " >> many1 (checkColGt >> ident)
def openDecl         :=
  withAntiquot (mkAntiquot "openDecl" `Lean.Parser.Command.openDecl (isPseudoKind := true)) <|
    openHiding <|> openRenaming <|> openOnly <|> openSimple <|> openScoped
@[builtin_command_parser] def «open»    := leading_parser
  withPosition ("open " >> openDecl)

@[builtin_command_parser] def «mutual» := leading_parser
  "mutual " >> many1 (ppLine >> notSymbol "end" >> commandParser) >>
  ppDedent (ppLine >> "end") >> terminationSuffix
def initializeKeyword := leading_parser
  "initialize " <|> "builtin_initialize "
@[builtin_command_parser] def «initialize» := leading_parser
  declModifiers false >> initializeKeyword >>
  optional (atomic (ident >> Term.typeSpec >> Term.leftArrow)) >> Term.doSeq

@[builtin_command_parser] def «in»  := trailing_parser withOpen (" in " >> commandParser)

@[builtin_command_parser] def addDocString := leading_parser
  docComment >> "add_decl_doc" >> ident

/--
  This is an auxiliary command for generation constructor injectivity theorems for
  inductive types defined at `Prelude.lean`.
  It is meant for bootstrapping purposes only. -/
@[builtin_command_parser] def genInjectiveTheorems := leading_parser
  "gen_injective_theorems% " >> ident

@[run_builtin_parser_attribute_hooks] abbrev declModifiersF := declModifiers false
@[run_builtin_parser_attribute_hooks] abbrev declModifiersT := declModifiers true

builtin_initialize
  register_parser_alias (kind := ``declModifiers) "declModifiers"       declModifiersF
  register_parser_alias (kind := ``declModifiers) "nestedDeclModifiers" declModifiersT
  register_parser_alias                                                 declId
  register_parser_alias                                                 declSig
  register_parser_alias                                                 declVal
  register_parser_alias                                                 optDeclSig
  register_parser_alias                                                 openDecl
  register_parser_alias                                                 docComment

end Command

namespace Term
/--
`open Foo in e` is like `open Foo` but scoped to a single term.
It makes the given namespaces available in the term `e`.
-/
@[builtin_term_parser] def «open» := leading_parser:leadPrec
  "open " >> Command.openDecl >> withOpenDecl (" in " >> termParser)

/--
`set_option opt val in e` is like `set_option opt val` but scoped to a single term.
It sets the option `opt` to the value `val` in the term `e`.
-/
@[builtin_term_parser] def «set_option» := leading_parser:leadPrec
  "set_option " >> ident >> ppSpace >> Command.optionValue >> " in " >> termParser
end Term

namespace Tactic
/-- `open Foo in tacs` (the tactic) acts like `open Foo` at command level,
but it opens a namespace only within the tactics `tacs`. -/
@[builtin_tactic_parser] def «open» := leading_parser:leadPrec
  "open " >> Command.openDecl >> withOpenDecl (" in " >> tacticSeq)

/-- `set_option opt val in tacs` (the tactic) acts like `set_option opt val` at the command level,
but it sets the option only within the tactics `tacs`. -/
@[builtin_tactic_parser] def «set_option» := leading_parser:leadPrec
  "set_option " >> ident >> ppSpace >> Command.optionValue >> " in " >> tacticSeq
end Tactic

end Parser
end Lean
