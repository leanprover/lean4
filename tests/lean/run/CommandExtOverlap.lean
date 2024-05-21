syntax (name := mycheck) "#check" sepBy(term, ",") : command

open Lean

macro_rules (kind := mycheck)
| `(#check $es,*) =>
  let cmds := es.getElems.map $ fun e => mkNode `Lean.Parser.Command.check #[mkAtom "#check", e]
  pure $ mkNullNode cmds

/-- info: Bool.true : Bool -/
#guard_msgs in
#check true

/--
info: Bool.true : Bool
---
info: Bool.true : Bool
-/
#guard_msgs in
#check true, true

/--
info: Bool.true : Bool
---
info: 1 : Nat
---
info: 3 : Nat
---
info: fun x => x + 1 : Nat → Nat
-/
#guard_msgs in
#check true, 1, 3, fun (x : Nat) => x + 1
