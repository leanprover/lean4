module
import Lean
public meta import Lean.Elab.Tactic

open Lean.Grind
open Lean.Grind.CommRing

-- Convenient RArray literals
elab tk:"#R[" ts:term,* "]" : term => do
  let ts : Array Lean.Syntax := ts
  let es ← ts.mapM fun stx => Lean.Elab.Term.elabTerm stx none
  if h : 0 < es.size then
    Lean.RArray.toExpr (← Lean.Meta.inferType es[0]!) id (Lean.RArray.ofArray es h)
  else
    throwErrorAt tk "RArray cannot be empty"

example (x y : Int) : (x + y) * (x + y + 1) = x * (1 + y + x) + (y + 1 + x) * y :=
  let ctx := #R[x, y]
  let lhs : Expr := .mul (.add (.var 0) (.var 1)) (.add (.add (.var 0) (.var 1)) (.num 1))
  let rhs : Expr := .add (.mul (.var 0) (.add (.add (.num 1) (.var 1)) (.var 0)))
                         (.mul (.add (.add (.var 1) (.num 1)) (.var 0)) (.var 1))
  Expr.eq_of_toPoly_eq ctx lhs rhs (Eq.refl true)

example (x y : UInt8) : (128 * x + y) * 2 = y + y :=
  let ctx := #R[x, y]
  let lhs : Expr := .mul (.add (.mul (.num 128) (.var 0)) (.var 1)) (.num 2)
  let rhs : Expr := .add (.var 1) (.var 1)
  Expr.eq_of_toPolyC_eq ctx lhs rhs (Eq.refl true)
