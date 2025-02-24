import Lean

open Int.Linear

-- Convenient RArray literals
elab tk:"#R[" ts:term,* "]" : term => do
  let ts : Array Lean.Syntax := ts
  let es ← ts.mapM fun stx => Lean.Elab.Term.elabTerm stx none
  if h : 0 < es.size then
    return (Lean.RArray.toExpr (← Lean.Meta.inferType es[0]!) id (Lean.RArray.ofArray es h))
  else
    throwErrorAt tk "RArray cannot be empty"

example (x₁ x₂ : Int) :
  Expr.denote #R[x₁, x₂] (.add (.add (.var 0) (.var 1)) (.num 3))
  =
  x₁ + x₂ + 3  :=
  rfl

example (x₁ x₂ : Int) :
  Poly.denote #R[x₁, x₂] (.add 1 0 (.add 3 1 (.num 4)))
  =
  1 * x₁ + ((3 * x₂) + 4) :=
  rfl

example (x₁ x₂ : Int) :
  Expr.denote #R[x₁, x₂] (.sub (.add (.mulR (.var 0) 4) (.mulL 2 (.var 1))) (.num 3))
  =
  (x₁*4) + 2*x₂ - 3 :=
  rfl

example :
  Expr.norm (.add (.add (.var 1) (.var 1)) (.num 3))
  =
  Expr.norm (.add (.num 3) (.mulL 2 (.var 1))) :=
  rfl

example :
  Expr.norm (.add (.add (.add (.var 1) (.var 1)) (.num 3)) (.var 2))
  =
  Expr.norm (.add (.add (.num 3) (.var 2)) (.mulL 2 (.var 1))) :=
  rfl

example (x₁ x₂ x₃ : Int) :
  (Expr.denote #R[x₁, x₂, x₃] (.sub (.add (.mulR (.var 0) 4) (.mulL 2 (.var 1))) (.num 3))
  =
  Expr.denote #R[x₁, x₂, x₃] (.sub (.var 1) (.var 2)))
  =
  ((x₁*4) + 2*x₂ - 3 = x₂ - x₃) :=
  rfl

example :
  Expr.norm (.sub (.sub (.add (.mulR (.var 0) 4) (.mulL 2 (.var 1))) (.num 3)) (.sub (.var 1) (.var 2)))
  =
  Expr.norm (.sub (.add (.var 2) (.add (.var 1) (.add (.mulL 4 (.var 0)) (.num (-3))))) (.num 0)) :=
  rfl

example (x₁ x₂ x₃ : Int) : (x₁ + x₂) + (x₂ + x₃) = x₃ + 2*x₂ + x₁ :=
  Expr.eq_of_norm_eq #R[x₁, x₂, x₃]
   (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
   (.add 1 2 (.add 2 1 (.add 1 0 (.num 0))))
   rfl

example :
  Expr.norm
    (.sub (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
          (Expr.add (Expr.var 2) (Expr.var 1)))
  =
  Expr.norm
    (.sub (Expr.add (Expr.var 0) (Expr.var 1))
          (Expr.num 0))
  :=
  rfl

example (x₁ x₂ x₃ : Int) : ((x₁ + x₂) + (x₂ + x₃) = x₃ + x₂) = (x₁ + x₂ = 0) :=
  Int.Linear.norm_eq #R[x₃, x₂, x₁]
    (Expr.add (Expr.add (Expr.var 2) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 0)))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (.add 1 2 (.add 1 1 (.num 0)))
    rfl

example (x₁ x₂ x₃ : Int) : ((x₁ + x₂) + (x₂ + x₃) ≤ x₃ + x₂) = (x₁ + x₂ ≤ 0) :=
  Int.Linear.norm_le #R[x₃, x₂, x₁]
    (Expr.add (Expr.add (Expr.var 2) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 0)))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (.add 1 2 (.add 1 1 (.num 0)))
    rfl
