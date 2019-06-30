import init.lean.parser.parser
open Lean
open Lean.Parser

namespace Foo

@[builtinTestParser] def pairParser :=
parser! "(" >> numLit >> "," >> ident >> ")"

@[builtinTestParser] def pairsParser :=
parser! "{" >> sepBy1 testParser "," >> "}"

@[builtinTestParser] def functionParser :=
parser! "fun" >> ident >> "," >> testParser

@[builtinTestParser] def identParser : Parser :=
ident

@[builtinTestParser] def numParser : Parser :=
numLit

@[builtinTestParser] def strParser : Parser :=
strLit

end Foo

def testParser (input : String) : IO Unit :=
do
env ← mkEmptyEnvironment;
testPTables ← builtinTestParsingTable.get;
stx ← IO.ofExcept $ runParser env testPTables input;
IO.println stx

def main (xs : List String) : IO Unit :=
do
testParser "(10, hello)";
testParser "{ hello, 400, \"hello\", (10, hello), /- comment -/ (20, world), { fun x, (10, hello) }, { (30, foo) } }";
-- Following example has syntax error
testParser
"{ hello, 400, \"hello\", (10, hello), /- comment -/ (20, world), { fun x, [ (10, hello) }, { (30, foo) } }"
