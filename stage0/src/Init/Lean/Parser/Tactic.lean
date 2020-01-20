/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Parser.Term

namespace Lean
namespace Parser

@[init] def regBuiltinTacticParserAttr : IO Unit :=
let leadingIdentAsSymbol := true;
registerBuiltinParserAttribute `builtinTacticParser `tactic leadingIdentAsSymbol

@[init] def regTacticParserAttribute : IO Unit :=
registerBuiltinDynamicParserAttribute `tacticParser `tactic

@[inline] def tacticParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
categoryParser `tactic rbp

namespace Tactic

def underscoreFn {k : ParserKind} : ParserFn k :=
fun a c s =>
  let s   := symbolFn "_" a c s;
  let stx := s.stxStack.back;
  let s   := s.popSyntax;
  s.pushSyntax $ mkIdentFrom stx `_

@[inline] def underscore {k : ParserKind} : Parser k :=
{ fn   := underscoreFn,
  info := mkAtomicInfo "ident" }

def ident' : Parser := ident <|> underscore

def seq := parser! sepBy tacticParser "; " true

@[builtinTacticParser] def «intro»      := parser! nonReservedSymbol "intro " >> optional ident'
@[builtinTacticParser] def «intros»     := parser! nonReservedSymbol "intros " >> many ident'
@[builtinTacticParser] def «assumption» := parser! nonReservedSymbol "assumption"
@[builtinTacticParser] def «apply»      := parser! nonReservedSymbol "apply " >> termParser
@[builtinTacticParser] def «exact»      := parser! nonReservedSymbol "exact " >> termParser
@[builtinTacticParser] def «refine»     := parser! nonReservedSymbol "refine " >> termParser
@[builtinTacticParser] def «case»       := parser! nonReservedSymbol "case " >> ident >> tacticParser
@[builtinTacticParser] def «try»        := parser! nonReservedSymbol "try " >> tacticParser
@[builtinTacticParser] def «repeat»     := parser! nonReservedSymbol "repeat " >> tacticParser
@[builtinTacticParser] def «allGoals»   := parser! nonReservedSymbol "allGoals " >> tacticParser
@[builtinTacticParser] def «skip»       := parser! nonReservedSymbol "skip"
@[builtinTacticParser] def «traceState» := parser! nonReservedSymbol "traceState"

@[builtinTacticParser] def paren        := parser! "(" >> seq >> ")"
@[builtinTacticParser] def nestedTacticBlock := parser! "begin " >> seq >> "end"
@[builtinTacticParser] def nestedTacticBlockCurly := parser! "{" >> seq >> "}"
@[builtinTacticParser] def orelse := tparser! pushLeading >> " <|> " >> tacticParser 1

end Tactic

namespace Term

@[builtinTermParser] def tacticBlock := parser! symbol "begin " appPrec >> Tactic.seq >> "end"
-- Use `unboxSingleton` trick similar to the one used at Command.lean for `Term.stxQuot`
@[builtinTermParser] def tacticStxQuot : Parser := node `Lean.Parser.Term.stxQuot $ symbol "`(tactic|" appPrec >> sepBy1 tacticParser "; " true true >> ")"

end Term

end Parser
end Lean
