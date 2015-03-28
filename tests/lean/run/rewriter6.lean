import data.int
open int

theorem abs_thm1 (a b : int) : a - b = a + -b :=
by rewrite ↑sub -- unfold sub

theorem abs_thm2 (a b : int) : a - b = a + -b :=
by rewrite ^sub -- unfold sub

definition double (x : int) := x + x

theorem double_zero (x : int) : double (0 + x) = (1 + 1)*x :=
by rewrite [↑double, zero_add, mul.right_distrib, one_mul]
