set_option cbv.warning false

-- Case 1: p is literally True/False
theorem test1 : decide True = true := by cbv
theorem test2 : decide False = false := by cbv

/--
info: theorem test1 : decide True = true :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (decide_true instDecidableTrue)) true) (eq_self true))
-/
#guard_msgs in
#print test1

/--
info: theorem test2 : decide False = false :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (decide_false instDecidableFalse)) false) (eq_self false))
-/
#guard_msgs in
#print test2

-- Case 2: p simplifies to True/False
theorem test3 : decide (1 < 2) = true := by cbv
theorem test4 : decide (3 < 2) = false := by cbv

/--
info: theorem test3 : decide (1 < 2) = true :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq (Lean.Sym.decide_prop_eq_true (1 < 2) (Lean.Sym.Nat.lt_eq_true 1 2 (eagerReduce (Eq.refl true)))))
      true)
    (eq_self true))
-/
#guard_msgs in
#print test3

/--
info: theorem test4 : decide (3 < 2) = false :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq (Lean.Sym.decide_prop_eq_false (3 < 2) (Lean.Sym.Nat.lt_eq_false 3 2 (eagerReduce (Eq.refl false)))))
      false)
    (eq_self false))
-/
#guard_msgs in
#print test4

/--
trace: x : Nat
⊢ decide (x = 4) = true
---
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem test5 : decide (x = (2 + 2)) = true := by
  cbv
  trace_state
  sorry
