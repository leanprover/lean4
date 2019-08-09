import init.lean.parser
import init.lean.parser.transform
open Lean
open Lean.Parser

def fixEqnSyntax (stx : Syntax) : Syntax :=
stx.rewriteBottomUp $ fun stx =>
  stx.ifNodeKind `Lean.Parser.Term.equation3
    (fun stx =>
       let args := stx.getArgs;
       let args := args.modify 1 $ fun patterns =>
         let patterns := patterns.asNode.modifyArgs $ fun args => args.map Syntax.removeParen;
         patterns.manyToSepBy ",";
       let args := args.modify 2 $ fun assignTk => assignTk.setAtomVal "=>";
       Syntax.node `Lean.Parser.Term.matchAlt args)
    (fun _ => stx)

def main (xs : List String) : IO Unit :=
do
[fname] ← pure xs | throw (IO.userError "usage `patch <file-name>`");
env ← mkEmptyEnvironment;
stx ← parseFile env fname;
let stx := fixEqnSyntax stx;
match stx.reprint with
| some out => IO.print out
| none     => throw (IO.userError "failed to reprint")
