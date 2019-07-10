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

def testParserFailure (input : String) : IO Unit :=
do
env ← mkEmptyEnvironment;
termPTables ← builtinTermParsingTable.get;
match runParser env termPTables input "<input>" "expr" with
| Except.ok stx    => throw (IO.userError ("unexpected success\n" ++ toString stx))
| Except.error msg => IO.println ("failed as expected, error: " ++ msg)

def testFailures (is : List String) : IO Unit :=
is.mfor $ fun input => do
  IO.println input;
  testParserFailure input

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
"{ Prod . fst := 10, .. }",
"a[i]",
"f [10, 20]",
"g a[x+2]",
"g f.a.1.2.bla x.1.a",
"x+y*z < 10/3",
"id (α := Nat) 10",
"(x : a)",
"a -> b",
"{x : a} -> b",
"{a : Type} -> [HasToString a] -> (x : a) -> b",
"f ({x : a} -> b)",
"f (x : a) -> b",
"f ((x : a) -> b)",
"(f : (n : Nat) → Vector Nat n) -> Nat",
"∀ x y (z : Nat), x > y -> x > y - z",
"
match x with
| some x => true
| none => false",
"
match x with
| some y => match y with
  | some (a, b) => a + b
  | none        => 1
| none => 0
"
];
testFailures [
"f {x : a} -> b",
"(x := 20)"
]
