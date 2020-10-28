import Lean.Parser.Command
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
"/-- doc string test -/   private theorem bla (x : Nat) : x = x := Eq.refl x",
"class Alternative (f : Type u → Type v) extends Applicative f : Type (max (u+1) v) :=
(failure : ∀ {α : Type u}, f α)
(orelse  : ∀ {α : Type u}, f α → f α → f α)
",
"local attribute [instance] foo bla",
"attribute [inline] test",
"open Lean (hiding Name)",
"reserve infixr ` ∨ `:30",
"reserve prefix `¬`:40",
"infixr ` ^ ` := Pow.pow",
"notation f ` $ `:1 a:0 := f a",
"notation `Prop` := Sort 0",
"notation `∅`   := EmptyCollection.emptyc _",
"notation `⟦`:max a `⟧`:0 := Quotient.mk a"
]
