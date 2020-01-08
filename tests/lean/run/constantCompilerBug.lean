import Init.Lean

new_frontend

open Lean
open Lean.Parser

def mkParserAttribute : IO ParserAttribute :=
registerParserAttribute (mkNameSimple "bla") "bla" "bla parser" Option.none

@[init mkParserAttribute]
constant parserAttribute : ParserAttribute

@[inline] def parser {k : ParserKind} : Parser k :=
Parser.mk (Parser.info $ Inhabited.default Parser) (fun _ => ParserAttribute.runParserFn parserAttribute (0 : Nat))

#check @parser
