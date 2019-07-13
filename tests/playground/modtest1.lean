import init.lean.parser.module
open Lean
open Lean.Parser

partial def parseCommands (displayStx : Bool) : ModuleReader → IO Unit
| r :=
  if r.isEOI then
    r.messages.toList.mfor $ fun msg => IO.println msg
  else do
    let (stx, r) := r.nextCommand;
    when displayStx (IO.println stx);
    parseCommands r

def testParser (input : String) (displayStx := true) : IO Unit :=
do
env ← mkEmptyEnvironment;
let (stx, reader) := mkModuleReader env input "<input>";
when displayStx (IO.println stx);
parseCommands displayStx reader

def main (xs : List String) : IO Unit :=
do
testParser "
prelude
import init.core
"

/-
universes u v

class Alternative (f : Type u → Type v) extends Applicative f : Type (max (u+1) v) :=
(failure : ∀ {α : Type u}, f α)
(orelse  : ∀ {α : Type u}, f α → f α → f α)
-/
