theorem ex1 (h : a = 5) :
   let_fun x := 1
   let_fun _y := 2
   let_fun _z := 3
   let_fun w := 4
   x + w = a := by
  simp -zeta only
  guard_target =ₛ
    let_fun x := 1;
    let_fun w := 4;
    x + w = a
  simp only
  guard_target =ₛ 1 + 4 = a
  simp [h]

theorem ex2 (h : a = 6) :
   let_fun x := 1
   let_fun _y := 2 + x
   let_fun _z := 3 + x
   let_fun w := 4 + x
   let_fun _z := 2 + w
   x + w = a := by
  simp -zeta only
  guard_target =ₛ
    let_fun x := 1;
    let_fun w := 4 + x;
    x + w = a
  simp only
  guard_target =ₛ 1 + (4 + 1) = a
  simp [h]
