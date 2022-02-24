open Nat.Linear

example (x₁ x₂ x₃ : Nat) : (x₁ + x₂) + (x₂ + x₃) = x₃ + 2*x₂ + x₁ :=
  Expr.eq_of_toNormPoly [x₁, x₂, x₃]
   (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
   (Expr.add (Expr.add (Expr.var 2) (Expr.mulL 2 (Expr.var 1))) (Expr.var 0))
   rfl

example (x₁ x₂ x₃ : Nat) : ((x₁ + x₂) + (x₂ + x₃) = x₃ + x₂) = (x₁ + x₂ = 0) :=
  Expr.of_cancel_eq [x₁, x₂, x₃]
    (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
    (Expr.add (Expr.var 2) (Expr.var 1))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (Expr.num 0)
    rfl

example (x₁ x₂ x₃ : Nat) : ((x₁ + x₂) + (x₂ + x₃) ≤ x₃ + x₂) = (x₁ + x₂ ≤ 0) :=
  Expr.of_cancel_le [x₁, x₂, x₃]
    (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
    (Expr.add (Expr.var 2) (Expr.var 1))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (Expr.num 0)
    rfl

example (x₁ x₂ x₃ : Nat) : ((x₁ + x₂) + (x₂ + x₃) < x₃ + x₂) = (x₁ + x₂ < 0) :=
  Expr.of_cancel_lt [x₁, x₂, x₃]
    (Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 1) (Expr.var 2)))
    (Expr.add (Expr.var 2) (Expr.var 1))
    (Expr.add (Expr.var 0) (Expr.var 1))
    (Expr.num 0)
    rfl

example (x₁ x₂ : Nat) : x₁ + 2 ≤ 3*x₂ → 4*x₂ ≤ 3 + x₁ → 3 ≤ 2*x₂ → False :=
  Certificate.of_combine_isUnsat [x₁, x₂]
    [ (1, { eq := false, lhs := Expr.add (Expr.var 0) (Expr.num 2), rhs := Expr.mulL 3 (Expr.var 1) }),
      (1, { eq := false, lhs := Expr.mulL 4 (Expr.var 1), rhs := Expr.add (Expr.num 3) (Expr.var 0) }),
      (0, { eq := false, lhs := Expr.num 3, rhs := Expr.mulL 2 (Expr.var 1) }) ]
    rfl

example (x : Nat) (xs : List Nat) : (sizeOf x < 1 + (1 + sizeOf x + sizeOf xs)) = True :=
  ExprCnstr.eq_true_of_isValid [sizeOf x, sizeOf xs]
    { eq := false, lhs := Expr.inc (Expr.var 0), rhs := Expr.add (Expr.num 1) (Expr.add (Expr.add (Expr.num 1) (Expr.var 0)) (Expr.var 1)) }
    rfl

example (x : Nat) (xs : List Nat) : (1 + (1 + sizeOf x + sizeOf xs) < sizeOf x) = False :=
  ExprCnstr.eq_false_of_isUnsat [sizeOf x, sizeOf xs]
    { eq := false, lhs := Expr.inc <| Expr.add (Expr.num 1) (Expr.add (Expr.add (Expr.num 1) (Expr.var 0)) (Expr.var 1)), rhs := Expr.var 0 }
    rfl
