example (x y : Int) : x + y + 2 + y = y + 1 + 1 + x + y := by
  simp +arith only

example (x y : Int) (h : x + y + 2 + y < y + 1 + 1 + x + y) : False := by
  simp +arith only at h

example (x y : Int) (h : x + y + 2 + y > y + 1 + 1 + x + y) : False := by
  simp +arith only at h

example (x y : Int) (_h : x + y + 3 + y > y + 1 + 1 + x + y) : True := by
  simp +arith only at _h
  guard_hyp _h : True
  constructor

example (x y : Int) (h : x + y + 2 + y > 1 + 1 + x + x + y + 2*x) : 3*x + -1*y+1 ≤ 0 := by
  simp +arith only at h
  guard_hyp h : 3 * x + -1*y + 1 ≤ 0
  assumption

example (x y : Int) (h : 6*x + y + 3 + y + 1 < y + 1 + 1 + x + 5*y) : 5*x + -4*y + 3 ≤ 0 := by
  simp +arith only at h
  guard_hyp h : 5*x + -4*y + 3 ≤ 0
  assumption

example (x y : Int) : x + y + 2 + y ≤ y + 1 + 1 + x + y := by
  simp +arith only

example (x y : Int) : x + y + 2 + y ≤ y + 1 + 1 + 5 + x + y := by
  simp +arith only

example (x y z : Int) : x + y + 2 + y + z + z ≤ y + 3*z + 1 + 1 + x + y - z := by
  simp +arith only

example (x y : Int) (h : False) : x + y + 20 + y ≤ y + 1 + 1 + 5 + x + y := by
  simp +arith only
  guard_target = False
  assumption

example (x y : Int) (h : False) : x = y := by
  fail_if_success simp +arith only
  guard_target = x = y
  contradiction

example (x : Int) (h : False) : x = 3 := by
  fail_if_success simp +arith only
  guard_target = x = 3
  contradiction

example (x : Int) (h : False) : 3 = x := by
  fail_if_success simp +arith only
  guard_target = 3 = x
  contradiction

example (x : Int) (h : False) : 2*x = x + 3 := by
  simp +arith only
  guard_target = x = 3
  contradiction

example (x y : Int) (h : False) : 2*x = x + y := by
  simp +arith only
  guard_target = x = y
  contradiction

example (x : Int) (h : False) : 2*x + 1 = x := by
  simp +arith only
  guard_target = x = -1
  contradiction

example (x : Int) (h : False) (f : Int → Int) : f (0 + x + x) = 3 := by
  simp +arith only
  guard_target = f (2*x) = 3
  contradiction

example (x y : Int) (h : False) (f : Int → Int) : f (x + y - x) = 3 := by
  simp +arith only
  guard_target = f y = 3
  contradiction

example (x y : Int) (h : False) (f : Int → Int) : f (x + y - x + 2 - y + 1) = 3 := by
  simp +arith only
  guard_target = f 3 = 3
  contradiction

example (x y : Int) (h : False) (f : Int → Int) : f (x + y - x + (2 - y)*2 + 1) = 3 := by
  simp +arith only
  guard_target = f (-1*y + 5) = 3
  contradiction

example (x y : Int) (h : False) (f : Int → Int) : f (x + y - x + (2 - y)*(1+1) + 1) = 3 := by
  simp +arith only [Int.reduceAdd]
  guard_target = f (-1*y + 5) = 3
  contradiction

example (x y : Int) (h : False) (f : Int → Int) : f (x + y - x + (1-1+2)*(2 - y) + 1) = 3 := by
  simp +arith only [Int.reduceAdd, Int.reduceSub]
  guard_target = f (-1*y + 5) = 3
  contradiction

example (x y : Int) (h : False) (f : Int → Int) : f (Int.add x y - x + (2 - y)*2 + 1) = 3 := by
  simp +arith only
  guard_target = f (-1*y + 5) = 3
  contradiction

example (x y : Int) (h : False) (f : Int → Int) : f (x + y - x + Int.mul (1-1+2) (2 - y) + 1) = 3 := by
  simp +arith only [Int.reduceAdd, Int.reduceSub]
  guard_target = f (-1*y + 5) = 3
  contradiction

example (x y : Int) (h : False) (f : Int → Int) : f (Int.add x y - x + (2 - y)*(-2) + 1) = 3 := by
  simp +arith only
  guard_target = f (3*y + -3) = 3
  contradiction

example (x : Int) : x > x - 1 := by
  simp +arith only

example (x : Int) : x - 1 < x := by
  simp +arith only

example (x : Int) : x < x + 1 := by
  simp +arith only

example (x : Int) : x ≥ x - 1 := by
  simp +arith only

example (x : Int) : x ≤ x := by
  simp +arith only

example (x : Int) : x ≤ x + 1 := by
  simp +arith only

example (x : Int) (h : False) : x > x := by
  simp +arith only
  guard_target = False
  assumption

theorem ex₁ (x y z : Int) : x + y + 2 + y + z + z ≤ y + 3*z + 1 + 1 + x + y - z := by
  simp +arith only

/--
info: theorem ex₁ : ∀ (x y z : Int), x + y + 2 + y + z + z ≤ y + 3 * z + 1 + 1 + x + y - z :=
fun x y z =>
  of_eq_true
    (id
      (Int.Linear.ExprCnstr.eq_true_of_isValid
        (Lean.RArray.branch 1 (Lean.RArray.leaf x) (Lean.RArray.branch 2 (Lean.RArray.leaf y) (Lean.RArray.leaf z)))
        (Int.Linear.ExprCnstr.le
          ((((((Int.Linear.Expr.var 0).add (Int.Linear.Expr.var 1)).add (Int.Linear.Expr.num 2)).add
                    (Int.Linear.Expr.var 1)).add
                (Int.Linear.Expr.var 2)).add
            (Int.Linear.Expr.var 2))
          (((((((Int.Linear.Expr.var 1).add (Int.Linear.Expr.mulL 3 (Int.Linear.Expr.var 2))).add
                            (Int.Linear.Expr.num 1)).add
                        (Int.Linear.Expr.num 1)).add
                    (Int.Linear.Expr.var 0)).add
                (Int.Linear.Expr.var 1)).sub
            (Int.Linear.Expr.var 2)))
        (Eq.refl true)))
-/
#guard_msgs (info) in
#print ex₁

theorem ex₂ (x y z : Int) (f : Int → Int) : x + f y + 2 + f y + z + z ≤ f y + 3*z + 1 + 1 + x + f y - z := by
  simp +arith only

/--
info: theorem ex₂ : ∀ (x y z : Int) (f : Int → Int), x + f y + 2 + f y + z + z ≤ f y + 3 * z + 1 + 1 + x + f y - z :=
fun x y z f =>
  of_eq_true
    ((fun x_1 =>
        id
          (Int.Linear.ExprCnstr.eq_true_of_isValid
            (Lean.RArray.branch 1 (Lean.RArray.leaf x)
              (Lean.RArray.branch 2 (Lean.RArray.leaf x_1) (Lean.RArray.leaf z)))
            (Int.Linear.ExprCnstr.le
              ((((((Int.Linear.Expr.var 0).add (Int.Linear.Expr.var 1)).add (Int.Linear.Expr.num 2)).add
                        (Int.Linear.Expr.var 1)).add
                    (Int.Linear.Expr.var 2)).add
                (Int.Linear.Expr.var 2))
              (((((((Int.Linear.Expr.var 1).add (Int.Linear.Expr.mulL 3 (Int.Linear.Expr.var 2))).add
                                (Int.Linear.Expr.num 1)).add
                            (Int.Linear.Expr.num 1)).add
                        (Int.Linear.Expr.var 0)).add
                    (Int.Linear.Expr.var 1)).sub
                (Int.Linear.Expr.var 2)))
            (Eq.refl true)))
      (f y))
-/
#guard_msgs (info) in
#print ex₂

example (x y : Int) (h : False) : 2*x = x + y := by
  simp +arith only
  guard_target = x = y
  contradiction

example (x y : Int) (h : 2*x + 2*y = 4) : x + y = 2 := by
  simp +arith only at h
  guard_hyp h : x + y + -2 = 0
  simp +arith
  assumption

example (x y : Int) (h : 6*x + 3*y = 9) : 2*x + y = 3 := by
  simp +arith only at h
  guard_hyp h : 2*x + y + -3 = 0
  simp +arith
  assumption

example (x y : Int) (h : 2*x - 2*y ≤ 4) : x - y ≤ 2 := by
  simp +arith only at h
  guard_hyp h : x + -1*y + -2 ≤ 0
  simp +arith
  assumption

example (x y : Int) (h : -6*x + 3*y = -9) : - 2*x = -3 - y := by
  simp +arith only at h
  guard_hyp h : -2*x + y + 3 = 0
  simp +arith
  assumption

example (x y : Int) (h : 3*x + 6*y = 2) : False := by
  simp +arith only at h

example (x : Int) (h : 3*x = 1) : False := by
  simp +arith only at h

example (x : Int) (h : 2*x = 1) : False := by
  simp +arith only at h

example (x : Int) (h : x + x = 1) : False := by
  simp +arith only at h

example (x y : Int) (h : x + x + x = 1 + 2*y + x) : False := by
  simp +arith only at h

example (x : Int) (h : -x - x = 1) : False := by
  simp +arith only at h

example (x : Int) (h : 2*x ≤ 1) : x ≤ 0 := by
  simp +arith only at h
  guard_hyp h : x ≤ 0
  assumption

example (x y : Int) (h : 6*x + y + y + y ≤ 7) : 2*x + y + -2 ≤ 0 := by
  simp +arith only at h
  guard_hyp h : 2*x + y + -2 ≤ 0
  assumption

example (x y : Int) (h : 5*x + y + y + y ≤ 7 - x) : 2*x + y + -2 ≤ 0 := by
  simp +arith only at h
  guard_hyp h : 2*x + y + -2 ≤ 0
  assumption

example (x : Int) : (11*x ≤ 10) ↔ (x ≤ 0) := by
  simp +arith only

example (x : Int) : (11*x > 10) ↔ (x ≥ 1) := by
  simp +arith only
