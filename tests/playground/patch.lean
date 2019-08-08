import init.lean.parser
open Lean
open Lean.Parser

def fixEqnSyntax (stx : Syntax) : Syntax :=
stx

def main (xs : List String) : IO Unit :=
do
[fname] ← pure xs | throw (IO.userError "usage `patch <file-name>`");
env ← mkEmptyEnvironment;
stx ← parseFile env fname;
let stx := fixEqnSyntax stx;
match stx.reprint with
| some out => IO.print out
| none     => throw (IO.userError "failed to reprint")
