import init.lean.parser.module
open Lean
open Lean.Parser

partial def parseCommands (env : Environment) (displayStx : Bool) : ModuleParser → IO ModuleParser
| p =>
  match parseCommand env p with
  | (stx, p) =>
    if isEOI stx then pure p
    else do
      when displayStx (IO.println stx);
      parseCommands p

def testParser (input : String) (displayStx := true) : IO Unit :=
do
env ← mkEmptyEnvironment;
let (stx, p) := mkModuleParser env input "<input>";
when displayStx (IO.println stx);
p ← parseCommands env displayStx p;
p.messages.toList.mfor $ fun msg => IO.println msg;
pure ()

def main (xs : List String) : IO Unit :=
do
testParser "
prelude
import init.core

universes u v
  def b : Type

class Alternative (f : Type u → Type v) extends Applicative f : Type (max (u+1) v) :=
(failure : ∀ {α : Type u}, f α)
(orelse  : ∀ {α : Type u}, f α → f α → f α)
"
