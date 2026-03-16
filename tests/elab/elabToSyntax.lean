import Lean.Elab.Term

open Lean Expr Elab Term

elab "lett " decl:letDecl ";" e:term : term <= ty? => do
  let elabE (ty? : Option Expr) : TermElabM Expr := do elabTerm e ty?
  elabToSyntax elabE fun body => do
    elabTerm (← `(let $decl:letDecl; $body)) ty?

#guard lett x := 42; (x + 1) = 43
