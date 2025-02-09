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
