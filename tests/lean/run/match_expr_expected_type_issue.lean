import Lean

open Lean Meta Simp

def foo' (e : Expr) : SimpM Step := do
  let_expr Neg.neg _ _ arg ← e | return .continue
  match_expr arg with
  | OfNat.ofNat _ _ _ => return .done { expr := e }
  | _ =>
    let some v ← getIntValue? arg | return .continue
    if v < 0 then
      return .done { expr := toExpr (- v) }
    else
      return .done { expr := toExpr v }
