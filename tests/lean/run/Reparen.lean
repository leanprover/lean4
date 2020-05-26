/-! Reprint file after removing all parentheses and then passing it through the parenthesizer -/
import Lean.PrettyPrinter.Parenthesizer

open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Format

def Substring.beq (ss1 ss2 : Substring) : Bool :=
ss1.toString == ss2.toString

instance : HasBeq Substring := ⟨Substring.beq⟩

partial def Lean.Syntax.structEq : Syntax → Syntax → Bool
| Syntax.missing, Syntax.missing => true
| Syntax.node k args, Syntax.node k' args' => k == k' && args.isEqv args' Lean.Syntax.structEq
| Syntax.atom _ val, Syntax.atom _ val' => val == val'
| Syntax.ident _ rawVal val preresolved, Syntax.ident _ rawVal' val' preresolved' => rawVal == rawVal' && val == val' && preresolved == preresolved'
| _, _ => false

instance : HasBeq Lean.Syntax := ⟨Lean.Syntax.structEq⟩

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

def main (args : List String) : IO Unit := do
let (debug, f) : Bool × String := match args with
  | [f, "-d"] => (true, f)
  | [f]       => (false, f)
  | _         => panic! "usage: file [-d]";
initSearchPath none;
env ← importModules [{module := `Lean.Parser}];
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
