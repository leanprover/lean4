theorem ex1 (h : a = 5) :
   have x := 1
   have _y := 2
   have _z := 3
   have w := 4
   x + w = a := by
  simp -zeta only
  guard_target =ₛ
    have x := 1;
    have w := 4;
    x + w = a
  simp only
  guard_target =ₛ 1 + 4 = a
  simp [h]

theorem ex2 (h : a = 6) :
   have x := 1
   have _y := 2 + x
   have _z := 3 + x
   have w := 4 + x
   have _z := 2 + w
   x + w = a := by
  simp -zeta only
  guard_target =ₛ
    have x := 1;
    have w := 4 + x;
    x + w = a
  simp only
  guard_target =ₛ 1 + (4 + 1) = a
  simp [h]
