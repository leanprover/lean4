import Std

-- Basic indexing
theorem test1 : #[1, 2, 3][0] = 1 := by cbv

/--
info: theorem test1 : #[1, 2, 3][0] = 1 :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.refl 1)) 1) (eq_self 1))
-/
#guard_msgs in
#print test1

theorem test2 : #[1, 2, 3][2] = 3 := by cbv

/--
info: theorem test2 : #[1, 2, 3][2] = 3 :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.refl 3)) 3) (eq_self 3))
-/
#guard_msgs in
#print test2

-- Optional indexing (in bounds)
theorem test3 : #[1, 2, 3][1]? = some 2 := by cbv

/--
info: theorem test3 : #[1, 2, 3][1]? = some 2 :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.refl (some 2))) (some 2)) (eq_self (some 2)))
-/
#guard_msgs in
#print test3

-- Optional indexing (out of bounds)
theorem test4 : #[1, 2, 3][5]? = none := by cbv

/--
info: theorem test4 : #[1, 2, 3][5]? = none :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.refl none)) none) (eq_self none))
-/
#guard_msgs in
#print test4

-- Nested arrays
theorem test5 : #[#[1, 2], #[3, 4]][1][0] = 3 := by cbv

/--
info: theorem test5 : #[#[1, 2], #[3, 4]][1][0] = 3 :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq
        (Eq.trans
          (GetElem.getElem.congr_simp { toList := [{ toList := [1, 2] }, { toList := [3, 4] }] }[1] { toList := [3, 4] }
            (Eq.refl { toList := [3, 4] }) 0 0 (Eq.refl 0) (of_decide_eq_true (id (Eq.refl true))))
          (Eq.refl 3)))
      3)
    (eq_self 3))
-/
#guard_msgs in
#print test5

-- Array of strings/other types
theorem test6 : #["a", "b", "c"][0] = "a" := by cbv

/--
info: theorem test6 : #["a", "b", "c"][0] = "a" :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.refl "a")) "a") (eq_self "a"))
-/
#guard_msgs in
#print test6
