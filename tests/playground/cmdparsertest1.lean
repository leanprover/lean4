import init.lean.parser.command
open Lean
open Lean.Parser

def testParser (input : String) : IO Unit :=
do
env ← mkEmptyEnvironment;
cmdPTables ← builtinCommandParsingTable.get;
stx ← IO.ofExcept $ runParser env cmdPTables input "<input>" "command";
IO.println stx

def test (is : List String) : IO Unit :=
is.mfor $ fun input => do
  IO.println input;
  testParser input

def main (xs : List String) : IO Unit :=
do
IO.println Command.declaration.info.firstTokens;
test [
"@[inline] def x := 2",
"protected def length.{u} {α : Type u} : List α → Nat
  | [] := 0
  | (a::as) := 1 + length as",
"/-- doc string test -/   private theorem bla (x : Nat) : x = x := Eq.refl x"
]
