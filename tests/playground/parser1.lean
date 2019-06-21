import init.lean.parser.parser
open Lean
open Lean.Parser

local infixl `>>`:50 := Lean.Parser.andthen

@[builtinTestParser] def pairParser : Parser :=
node `pairKind $
  "(" >> numLit >> "," >> ident >> ")"

@[builtinTestParser] def pairsParser : Parser :=
node `pairsKind $
  "{" >> sepBy1 testParser "," >> "}"

@[builtinTestParser] def functionParser : Parser :=
node `funKind $
  "fun" >> ident >> "," >> testParser

@[builtinTestParser] def identParser : Parser :=
ident

@[builtinTestParser] def numParser : Parser :=
numLit

@[builtinTestParser] def strParser : Parser :=
strLit

def testParser (input : String) : IO Unit :=
do
env ← mkEmptyEnvironment,
testPTables ← builtinTestParsingTable.get,
stx ← IO.ofExcept $ runParser env testPTables input,
IO.println stx

def main (xs : List String) : IO Unit :=
do
testParser "(10, hello)",
testParser "{ hello, 400, \"hello\", (10, hello), /- comment -/ (20, world), { fun x, (10, hello) }, { (30, foo) } }",
-- Following example has syntax error
testParser
"{ hello, 400, \"hello\", (10, hello), /- comment -/ (20, world), { fun x, [ (10, hello) }, { (30, foo) } }"
