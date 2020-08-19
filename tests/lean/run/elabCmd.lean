import Lean
open Lean
open Lean.Elab
open Lean.Elab.Term

def getCtors (c : Name) : TermElabM (List Name) := do
env ← getEnv;
match env.find? c with
| some (ConstantInfo.inductInfo val) =>
  pure val.ctors
| _ => pure []

def elabAnonCtor (args : Syntax) (τ : Expr) : TermElabM Expr := do
  match τ.getAppFn with
  | Expr.const C _ _ => do
    ctors ← getCtors C;
    match ctors with
    | [c] => do
      stx ← `($(Lean.mkIdent c) $(getSepElems args.getArgs)*);
      elabTerm stx τ
-- error handling
    | _ => unreachable!
  | _ => unreachable!

new_frontend

elab "foo⟨" args:(sepBy term ", ") "⟩" : term <= τ => do
  elabAnonCtor args τ

example : Nat × Nat := foo⟨1, 2⟩
