import init.lean.parser.parser
open Lean
open Lean.Parser

def mkPairKind : IO SyntaxNodeKind := nextKind `pair
@[init mkPairKind]
constant pairKind : SyntaxNodeKind := default _

def mkPairsKind : IO SyntaxNodeKind := nextKind `pairs
@[init mkPairsKind]
constant pairsKind : SyntaxNodeKind := default _

def mkFunKind : IO SyntaxNodeKind := nextKind `fun
@[init mkFunKind]
constant funKind : SyntaxNodeKind := default _

local infixl `>>`:50 := Lean.Parser.andthen

def pairParser : Parser :=
node pairKind $
  "(" >> number >> "," >> ident >> ")"

attribute [builtinTestParser] pairParser

def pairsParser : Parser :=
node pairsKind $
  "{" >> many1 testParser >> "}"

attribute [builtinTestParser] pairsParser

def functionParser : Parser :=
node funKind $
  "fun" >> ident >> "," >> testParser

attribute [builtinTestParser] functionParser

def testParser (input : String) : IO Unit :=
do
env ← mkEmptyEnvironment,
testPTables ← builtinTestParsingTable.get,
stx ← IO.ofExcept $ runParser env testPTables input,
IO.println stx

def main (xs : List String) : IO Unit :=
do
testParser "(10, hello)",
testParser "{ (10, hello) /- comment -/ (20, world) { fun x, (10, hello) } { (30, foo) } }"
