import Lean

open Nat.Linear

-- Convenient RArray literals
elab tk:"#R[" ts:term,* "]" : term => do
  let ts : Array Lean.Syntax := ts
  let es ← ts.mapM fun stx => Lean.Elab.Term.elabTerm stx none
  if h : 0 < es.size then
    return (Lean.RArray.toExpr (← Lean.Meta.inferType es[0]!) id (Lean.RArray.ofArray es h))
  else
    throwErrorAt tk "RArray cannot be empty"


example (x₁ x₂ x₃ : Nat) : (x₁ + x₂) + (x₂ + x₃) = x₃ + 2*x₂ + x₁ :=
  Expr.eq_of_toNormPoly #R[x₁, x₂, x₃]
   (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
   (Expr.add (Expr.add (Expr.var 2) (Expr.mulL 2 (Expr.var 1))) (Expr.var 0))
   rfl

example (x₁ x₂ x₃ : Nat) : ((x₁ + x₂) + (x₂ + x₃) = x₃ + x₂) = (x₁ + x₂ = 0) :=
  Expr.of_cancel_eq #R[x₁, x₂, x₃]
    (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
    (Expr.add (Expr.var 2) (Expr.var 1))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (Expr.num 0)
    rfl

example (x₁ x₂ x₃ : Nat) : ((x₁ + x₂) + (x₂ + x₃) ≤ x₃ + x₂) = (x₁ + x₂ ≤ 0) :=
  Expr.of_cancel_le #R[x₁, x₂, x₃]
    (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
    (Expr.add (Expr.var 2) (Expr.var 1))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (Expr.num 0)
    rfl

example (x₁ x₂ x₃ : Nat) : ((x₁ + x₂) + (x₂ + x₃) < x₃ + x₂) = (x₁ + x₂ < 0) :=
  Expr.of_cancel_lt #R[x₁, x₂, x₃]
    (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
    (Expr.add (Expr.var 2) (Expr.var 1))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (Expr.num 0)
    rfl

example (x : Nat) (xs : List Nat) : (sizeOf x < 1 + (1 + sizeOf x + sizeOf xs)) = True :=
  ExprCnstr.eq_true_of_isValid #R[sizeOf x, sizeOf xs]
    { eq := false, lhs := Expr.inc (Expr.var 0), rhs := Expr.add (Expr.num 1) (Expr.add (Expr.add (Expr.num 1) (Expr.var 0)) (Expr.var 1)) }
    rfl

example (x : Nat) (xs : List Nat) : (1 + (1 + sizeOf x + sizeOf xs) < sizeOf x) = False :=
  ExprCnstr.eq_false_of_isUnsat #R[sizeOf x, sizeOf xs]
    { eq := false, lhs := Expr.inc <| Expr.add (Expr.num 1) (Expr.add (Expr.add (Expr.num 1) (Expr.var 0)) (Expr.var 1)), rhs := Expr.var 0 }
    rfl
