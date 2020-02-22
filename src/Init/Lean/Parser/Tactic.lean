/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Parser.Term

namespace Lean
namespace Parser
namespace Tactic

def underscoreFn : ParserFn :=
fun c s =>
  let s   := symbolFn "_" c s;
  let stx := s.stxStack.back;
  let s   := s.popSyntax;
  s.pushSyntax $ mkIdentFrom stx `_

@[inline] def underscore : Parser :=
{ fn   := underscoreFn,
  info := mkAtomicInfo "ident" }

def ident' : Parser := ident <|> underscore

@[builtinTacticParser] def «intro»      := parser! nonReservedSymbol "intro " >> optional ident'
@[builtinTacticParser] def «intros»     := parser! nonReservedSymbol "intros " >> many ident'
@[builtinTacticParser] def «revert»     := parser! nonReservedSymbol "revert " >> many1 ident
@[builtinTacticParser] def «clear»      := parser! nonReservedSymbol "clear " >> many1 ident
@[builtinTacticParser] def «subst»      := parser! nonReservedSymbol "subst " >> many1 ident
@[builtinTacticParser] def «assumption» := parser! nonReservedSymbol "assumption"
@[builtinTacticParser] def «apply»      := parser! nonReservedSymbol "apply " >> termParser
@[builtinTacticParser] def «exact»      := parser! nonReservedSymbol "exact " >> termParser
@[builtinTacticParser] def «refine»     := parser! nonReservedSymbol "refine " >> termParser
@[builtinTacticParser] def «case»       := parser! nonReservedSymbol "case " >> ident >> tacticParser
@[builtinTacticParser] def «allGoals»   := parser! nonReservedSymbol "allGoals " >> tacticParser
@[builtinTacticParser] def «skip»       := parser! nonReservedSymbol "skip"
@[builtinTacticParser] def «traceState» := parser! nonReservedSymbol "traceState"
@[builtinTacticParser] def «generalize» := parser! nonReservedSymbol "generalize" >> optional (try (ident >> " : ")) >> termParser 50 >> " = " >> ident
def majorPremise := parser! optional (try (ident >> " : ")) >> termParser
def inductionAlt  : Parser := nodeWithAntiquot "inductionAlt" `Lean.Parser.Tactic.inductionAlt $ ident' >> many ident >> darrow >> termParser
def inductionAlts : Parser := withPosition $ fun pos => "|" >> sepBy1 inductionAlt (checkColGe pos.column "alternatives must be indented" >> "|")
def withAlts : Parser := optional (" with " >> inductionAlts)
def usingRec : Parser := optional (" using " >> ident)
def generalizingVars := optional (" generalizing " >> many1 ident)
@[builtinTacticParser] def «induction»  := parser! nonReservedSymbol "induction " >> majorPremise >> usingRec >> generalizingVars >> withAlts
@[builtinTacticParser] def paren        := parser! "(" >> nonEmptySeq >> ")"
@[builtinTacticParser] def nestedTacticBlock := parser! "begin " >> seq >> "end"
@[builtinTacticParser] def nestedTacticBlockCurly := parser! "{" >> seq >> "}"
@[builtinTacticParser] def orelse := tparser! " <|> " >> tacticParser 1

end Tactic
end Parser
end Lean
