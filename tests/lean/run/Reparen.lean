/-! Reprint file after removing all parentheses and then passing it through the parenthesizer -/
import Lean.Parser

open Lean
open Lean.Format

def unparenAux (parens body : Syntax) : Syntax :=
match parens.getHeadInfo, body.getHeadInfo, body.getTailInfo, parens.getTailInfo with
| some bi', some bi, some ti, some ti' => (body.setHeadInfo { bi with leading := bi'.leading }).setTailInfo { ti with trailing := ti'.trailing }
| _, _, _, _ => body

partial def unparen : Syntax → Syntax
-- don't remove parentheses in syntax quotation, they might be semantically significant
| stx => if stx.isOfKind `Lean.Parser.Term.stxQuot then stx
  else match_syntax stx with
  | `(($stx')) => unparenAux stx $ unparen stx'
  | `(level|($stx')) => unparenAux stx $ unparen stx'
  | _ => stx.modifyArgs $ Array.map unparen

unsafe def main (args : List String) : IO Unit := do
let (debug, f) : Bool × String := match args with
  | [f, "-d"] => (true, f)
  | [f]       => (false, f)
  | _         => panic! "usage: file [-d]";
initSearchPath none;
env ← mkEmptyEnvironment;
stx ← Lean.Parser.parseFile env args.head!;
let header := stx.getArg 0;
some s ← pure header.reprint | throw $ IO.userError "header reprint failed";
IO.print s;
let cmds := stx.getArgs.extract 1 stx.getArgs.size;
cmds.forM $ fun cmd => do
  let cmd := unparen cmd;
  (cmd, _) ← IO.runMeta (PrettyPrinter.parenthesizeCommand cmd)
    env { opts := KVMap.insert {} `trace.PrettyPrinter.parenthesize debug };
  some s ← pure cmd.reprint | throw $ IO.userError "cmd reprint failed";
  IO.print s

#eval main ["../../../src/Init/Core.lean"]
