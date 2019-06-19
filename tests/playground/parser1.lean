import init.lean.parser.parser
open Lean
open Lean.Parser

def mkPairKind : IO SyntaxNodeKind := nextKind `pair
@[init mkPairKind]
constant pairKind : SyntaxNodeKind := default _

def mkPairsKind : IO SyntaxNodeKind := nextKind `pairs
@[init mkPairsKind]
constant pairsKind : SyntaxNodeKind := default _

local infixl `>>`:50 := Lean.Parser.andthen

def pairParser : Parser :=
node pairKind $
  "(" >> number >> "," >> ident >> ")"

attribute [builtinTestParser] pairParser

def pairsParser : Parser :=
node pairsKind $
  "{" >> many testParser >> "}"

attribute [builtinTestParser] pairsParser

def testParser (input : String) : IO Unit :=
do
env ← mkEmptyEnvironment,
testPTables ← builtinTestParsingTable.get,
stx ← IO.ofExcept $ runParser env testPTables input,
IO.println stx

def main (xs : List String) : IO Unit :=
do
testParser "(10, hello)",
testParser "{ (10, hello) /- comment -/ (20, world) { } { (30, foo) } }"
