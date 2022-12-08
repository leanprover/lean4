import Lean

open Lean
open Lean.Elab
open Lean.Elab.Term

def f (stx : Syntax) : TermElabM Expr :=
  elabTerm _ _ _
