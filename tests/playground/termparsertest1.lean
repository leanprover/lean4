import init.lean.parser.term
open Lean
open Lean.Parser

def testParser (input : String) : IO Unit :=
do
env ← mkEmptyEnvironment;
termPTables ← builtinTermParsingTable.get;
stx ← IO.ofExcept $ runParser env termPTables input "<input>" "expr";
IO.println stx

def test (is : List String) : IO Unit :=
is.mfor $ fun input => do
  IO.println input;
  testParser input

def main (xs : List String) : IO Unit :=
do
test [
"Prod.mk",
"x.{u, v+1}",
"x.{u}",
"x",
"x.{max u v}",
"x.{max u v, 0}",
"f 0 1",
"f.{u+1} \"foo\" x",
"(f x, 0, 1)",
"()",
"(f x)",
"(f x : Type)",
"h (f x) (g y)",
"if x then f x else g x",
"if h : x then f x h else g x h",
"have p x y from f x; g this",
"suffices h : p x y from f x; g this",
"show p x y from f x",
"fun x y => f y x",
"fun (x y : Nat) => f y x",
"fun (x, y) => f y x",
"fun z (x, y) => f y x",
"fun ⟨x, y⟩ ⟨z, w⟩ => f y x w z",
"fun (Prod.mk x y) => f y x",
"{ x := 10, y := 20 }",
"{ x := 10, y := 20, }",
"{ x // p x 10 }",
"{ x : Nat // p x 10 }",
"{ .. }",
"{ Prod . fst := 10, .. }"
]
