new_frontend

syntax [mycheck] "#check" (sepBy term ",") : command

open Lean

macro_rules [mycheck]
| `(#check $es*) =>
  let cmds := es.getSepElems.map $ fun e => Syntax.node `Lean.Parser.Command.check #[Syntax.atom none "#check", e];
  pure $ mkNullNode cmds

#check true
#check true, true
#check true, 1, 3, fun (x : Nat) => x + 1
