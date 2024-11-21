-- A function that reduced badly, as a canary for kernel reduction
def bad (n : Nat) : Nat :=
  if h : n = 0 then 0 else bad (n / 2)
termination_by n

theorem foo : 2 * bad 42000 = bad 42000 + bad 42000 := by simp_arith

theorem foo' : Nat.mul 2 (bad 42000) = Nat.add (bad 42000) (bad 42000) := by simp_arith

theorem foo'' : Nat.mul 2 (bad 42000) = Nat.add (bad 42000) (bad 42000) := by omega


-- works
theorem foo1 : 2 * bad 42000 = bad 42000 + bad 42000 :=
  of_eq_true
    ((fun (x : Nat) =>
        @id ((2 * x = x + x) = True)
          (Nat.Linear.ExprCnstr.eq_true_of_isValid (Lean.RArray.leaf x)
            { eq := true, lhs := Nat.Linear.Expr.mulL 2 (Nat.Linear.Expr.var 0),
              rhs := (Nat.Linear.Expr.var 0).add (Nat.Linear.Expr.var 0) }
            (Eq.refl true)))
      (bad 42000))

-- fails
theorem foo2 : 2 * bad 42000 = bad 42000 + bad 42000 :=
  of_eq_true
    ((fun (x : Nat) =>
        @id ((Nat.mul 2 x = Nat.add x x) = True)
          (Nat.Linear.ExprCnstr.eq_true_of_isValid (Lean.RArray.leaf x)
            { eq := true, lhs := Nat.Linear.Expr.mulL 2 (Nat.Linear.Expr.var 0),
              rhs := (Nat.Linear.Expr.var 0).add (Nat.Linear.Expr.var 0) }
            (Eq.refl true)))
      (bad 42000))

-- fails
theorem foo4 : 2 * bad 42000 = bad 42000 + bad 42000 :=
  of_eq_true
    (@id ((2 * bad 42000 = bad 42000 + bad 42000) = True)
      (Nat.Linear.ExprCnstr.eq_true_of_isValid (Lean.RArray.leaf (bad 42000))
        { eq := true, lhs := Nat.Linear.Expr.mulL 2 (Nat.Linear.Expr.var 0),
          rhs := (Nat.Linear.Expr.var 0).add (Nat.Linear.Expr.var 0) }
        (Eq.refl true)))

-- fails
theorem foo5 : 2 * bad 42000 = bad 42000 + bad 42000 :=
  of_eq_true
    (@id ((Nat.mul 2 (bad 42000) = Nat.add (bad 42000) (bad 42000)) = True)
      (Nat.Linear.ExprCnstr.eq_true_of_isValid (Lean.RArray.leaf (bad 42000))
        { eq := true, lhs := Nat.Linear.Expr.mulL 2 (Nat.Linear.Expr.var 0),
          rhs := (Nat.Linear.Expr.var 0).add (Nat.Linear.Expr.var 0) }
        (Eq.refl true)))


theorem foo6 : 2 * bad 42000 = 0         := sorryAx ((Nat.mul 2 (bad 42000) = 0))
theorem foo7 : Nat.mul 2 (bad 42000) = 0 := sorryAx ((2 * (bad 42000) = 0))

theorem foo8 : (Nat.mul 2 (bad 42000) = Nat.add (bad 42000) (bad 42000)) :=
  of_eq_true
    (@id ((Nat.mul 2 (bad 42000) = Nat.add (bad 42000) (bad 42000)) = True)
      (Nat.Linear.ExprCnstr.eq_true_of_isValid (Lean.RArray.leaf (bad 42000))
        { eq := true, lhs := Nat.Linear.Expr.mulL 2 (Nat.Linear.Expr.var 0),
          rhs := (Nat.Linear.Expr.var 0).add (Nat.Linear.Expr.var 0) }
        (Eq.refl true)))
