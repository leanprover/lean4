import algebra.ring
open algebra eq.ops

variable {A : Type}

theorem zero_mul1 [s : ring A] (a : A) : 0 * a = 0 :=
have H : 0 * a + 0 = 0 * a + 0 * a,
  begin
    rewrite add_zero,
    rewrite -(add_zero 0) at {1},
    rewrite right_distrib
  end,
show 0 * a = 0, from (add.left_cancel H)⁻¹

theorem zero_mul2 [s : ring A] (a : A) : 0 * a = 0 :=
have H : 0 * a + 0 = 0 * a + 0 * a,
  by rewrite [add_zero, -(add_zero 0) at {1}, right_distrib],
show 0 * a = 0, from (add.left_cancel H)⁻¹
