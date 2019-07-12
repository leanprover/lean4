/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.lean.parser.term

namespace Lean
namespace Parser

@[init mkBuiltinParsingTablesRef]
constant builtinCommandParsingTable : IO.Ref ParsingTables := default _

@[init] def regBuiltinCommandParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinCommandParser `Lean.Parser.builtinCommandParsingTable

def commandParserFn {k : ParserKind} (rbp : Nat) : ParserFn k :=
fun _ => runBuiltinParser "command" builtinCommandParsingTable rbp

def commandParser (rbp : Nat := 0) : Parser :=
{ fn := commandParserFn rbp }

namespace Command
def commentBody : Parser :=
{ fn := rawFn (fun _ => finishCommentBlock 1) true }

def docComment       := parser! "/--" >> commentBody
def attrArg : Parser := ident <|> strLit <|> numLit
def attrInstance     := parser! ident >> many attrArg
def attributes       := parser! "@[" >> sepBy1 attrInstance ", " >> "]"
def «private»        := parser! "private"
def «protected»      := parser! "protected"
def visibility       := «private» <|> «protected»
def «noncomputable»  := parser! "noncomputable"
def «unsafe»         := parser! "unsafe"
def declModifiers    := parser! optional docComment >> optional «attributes» >> optional visibility >> optional «noncomputable» >> optional «unsafe»
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

@[builtinCommandParser] def declaration :=
declModifiers >> («abbrev» <|> «def» <|> «theorem» <|> «constant» <|> «instance» <|> «axiom» <|> «example»)

end Command

end Parser
end Lean
