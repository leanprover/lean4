import Lean

open Lean Meta

def f1 (e : Expr) : MetaM Expr := do
  match_expr (← whnf e) with
  | And a b => mkAppM ``And #[b, a]
  | _ => return e

def f2 (e : Expr) : MetaM Expr := do
  match_expr (meta := false) (← whnf e) with
  | And a b => mkAppM ``And #[b, a]
  | _ => return e
