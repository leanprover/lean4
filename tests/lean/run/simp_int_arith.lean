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
      (le_eq_true
        (Lean.RArray.branch 1 (Lean.RArray.leaf z) (Lean.RArray.branch 2 (Lean.RArray.leaf y) (Lean.RArray.leaf x)))
        ((((((Expr.var 2).add (Expr.var 1)).add (Expr.num 2)).add (Expr.var 1)).add (Expr.var 0)).add (Expr.var 0))
        (((((((Expr.var 1).add (Expr.mulL 3 (Expr.var 0))).add (Expr.num 1)).add (Expr.num 1)).add (Expr.var 2)).add
              (Expr.var 1)).sub
          (Expr.var 0))
        (Eq.refl true)))
-/
#guard_msgs (info) in
open Int.Linear in
#print ex₁

theorem ex₂ (x y z : Int) (f : Int → Int) : x + f y + 2 + f y + z + z ≤ f y + 3*z + 1 + 1 + x + f y - z := by
  simp +arith only

/--
info: theorem ex₂ : ∀ (x y z : Int) (f : Int → Int), x + f y + 2 + f y + z + z ≤ f y + 3 * z + 1 + 1 + x + f y - z :=
fun x y z f =>
  of_eq_true
    ((fun x_1 =>
        id
          (le_eq_true
            (Lean.RArray.branch 1 (Lean.RArray.leaf x_1)
              (Lean.RArray.branch 2 (Lean.RArray.leaf z) (Lean.RArray.leaf x)))
            ((((((Expr.var 2).add (Expr.var 0)).add (Expr.num 2)).add (Expr.var 0)).add (Expr.var 1)).add (Expr.var 1))
            (((((((Expr.var 0).add (Expr.mulL 3 (Expr.var 1))).add (Expr.num 1)).add (Expr.num 1)).add (Expr.var 2)).add
                  (Expr.var 0)).sub
              (Expr.var 1))
            (Eq.refl true)))
      (f y))
-/
#guard_msgs (info) in
open Int.Linear in
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

example (x y : Int) : (2*x + y + y = 4) ↔ (y + x = 2) := by
  simp +arith

example (x y : Int) : (2*x + y + y ≤ 3) ↔ (y + x ≤ 1) := by
  simp +arith

example (f : Int → Int) (x y : Int) : f (2*x + y) = f (y + x + x) := by
  simp +arith

example (a b : Int) : ¬ 2 ∣ 2*a + 4*b + 1 := by
  simp +arith

example (a b : Int) : ¬ 2 ∣ a + 3*b + 1 + b + a := by
  simp +arith

example (a b : Int) : ¬ 2 ∣ a + 3*b + 1 + b + 5*a := by
  simp +arith

example (a b : Int) : 2 ∣ 4*a + 6*b + 8 := by
  simp +arith

example (a b : Int) : 2 ∣ 2*(a + a) + (3+3)*(b + b) + 8 := by
  simp +arith

example (a : Int) : 16 ∣ 4*a + 32 ↔ 4 ∣ a + 8 := by
  simp +arith

example (a : Int) : 3 ∣ a + a + 1 + a + 1 + a ↔ 3 ∣ 4*a + 2 := by
  simp +arith

example (a : Int) : 2+1 ∣ a + a + 1 - a + 1 + a ↔ 3 ∣ 2*a + 2 := by
  simp +arith

example (a b : Int) : 6 ∣ a + 21 - a + 3*a + 6*b + 12 ↔ 2 ∣ a + 2*b + 11 := by
  simp +arith

theorem ex3 (a b : Int) : 6 ∣ a + (21 - a) + 3*(a + 2*b) + 12 ↔ 2 ∣ a + 2*b + 11 := by
  simp +arith

/--
info: theorem ex3 : ∀ (a b : Int), 6 ∣ a + (21 - a) + 3 * (a + 2 * b) + 12 ↔ 2 ∣ a + 2 * b + 11 :=
fun a b =>
  of_eq_true
    (Eq.trans
      (congrArg (fun x => x ↔ 2 ∣ a + 2 * b + 11)
        (id
          (norm_dvd_gcd (RArray.branch 1 (RArray.leaf b) (RArray.leaf a)) 6
            ((((Expr.var 1).add ((Expr.num 21).sub (Expr.var 1))).add
                  (Expr.mulL 3 ((Expr.var 1).add (Expr.mulL 2 (Expr.var 0))))).add
              (Expr.num 12))
            2 (Poly.add 1 1 (Poly.add 2 0 (Poly.num 11))) 3 (Eq.refl true))))
      (iff_self (2 ∣ a + 2 * b + 11)))
-/
#guard_msgs (info) in
open Lean in open Int.Linear in
#print ex3

theorem ex4 (a b : Int) : 6 ∣ a + (11 - a) + 3*(a + 2*b) - 11 ↔ 2 ∣ a + 2*b := by
  simp +arith

/--
info: theorem ex4 : ∀ (a b : Int), 6 ∣ a + (11 - a) + 3 * (a + 2 * b) - 11 ↔ 2 ∣ a + 2 * b :=
fun a b =>
  of_eq_true
    (Eq.trans
      (congr
        (congrArg Iff
          (Eq.trans
            (id
              (norm_dvd_gcd (RArray.branch 1 (RArray.leaf b) (RArray.leaf a)) 6
                ((((Expr.var 1).add ((Expr.num 11).sub (Expr.var 1))).add
                      (Expr.mulL 3 ((Expr.var 1).add (Expr.mulL 2 (Expr.var 0))))).sub
                  (Expr.num 11))
                2 (Poly.add 1 1 (Poly.add 2 0 (Poly.num 0))) 3 (Eq.refl true)))
            Init.Data.Int.DivMod.Lemmas._auxLemma.2))
        Init.Data.Int.DivMod.Lemmas._auxLemma.2)
      (iff_self (2 ∣ a)))
-/
#guard_msgs (info) in
open Lean in open Int.Linear in
#print ex4
