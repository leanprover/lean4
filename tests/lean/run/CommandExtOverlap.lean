syntax (name := mycheck) "#check" sepBy(term, ",") : command

open Lean

macro_rules (kind := mycheck)
| `(#check $es,*) =>
  let cmds := es.getElems.map $ fun e => Syntax.node `Lean.Parser.Command.check #[mkAtom "#check", e]
  pure $ mkNullNode cmds

#check true
#check true, true
#check true, 1, 3, fun (x : Nat) => x + 1
