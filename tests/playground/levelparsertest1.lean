import init.lean.parser.level
open Lean
open Lean.Parser

def testParser (input : String) : IO Unit :=
do
env ← mkEmptyEnvironment;
levelPTables ← builtinLevelParsingTable.get;
stx ← IO.ofExcept $ runParser env levelPTables input;
IO.println stx

def main (xs : List String) : IO Unit :=
do
testParser "max 0 1";
testParser "(1)";
testParser "u";
testParser "(u)";
testParser "(u+1)";
testParser "(u+1+2)";
testParser "(max u v w)";
testParser "imax u v";
testParser "(max (u+1) v)";
pure ()
