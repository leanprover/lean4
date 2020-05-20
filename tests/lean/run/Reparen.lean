/-! Reprint file after removing all parentheses and then passing it through the parenthesizer -/
import Init.Lean.PrettyPrinter.Parenthesizer

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
| stx => match_syntax stx with
  | `(($stx')) => unparenAux stx $ unparen stx'
  | `(level|($stx')) => unparenAux stx $ unparen stx'
  | _ => stx.modifyArgs $ Array.map unparen

def main (args : List String) : IO Unit := do
initSearchPath none;
env ← importModules [{module := `Init.Lean.Parser}];
stx ← Lean.Parser.parseFile env args.head!;
(stx', env) ← IO.runMeta (do
    let cmds := stx.getArgs.extract 1 stx.getArgs.size;
    args ← cmds.mapM $ PrettyPrinter.parenthesizeCommand ∘ unparen;
    pure $ stx.setArgs (#[stx.getArgs.get! 0] ++ args)
  )
  -- change to `true` for trace output
  env { opts := KVMap.insert {} `trace.PrettyPrinter.parenthesize false };
some s ← pure stx'.reprint | throw $ IO.userError "reprint failed";
true ← Parser.testModuleParser env s | throw $ IO.userError "reparse failed";
IO.print s

#eval main ["../../../src/Init/Core.lean"]
