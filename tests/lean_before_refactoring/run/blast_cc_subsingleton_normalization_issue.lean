import data.real
open real

namespace safe

definition pos (x : ℝ) := x > 0
constants (safe_log : Π (x : ℝ), pos x → ℝ)

lemma pos_add {x y : ℝ} : pos x →  pos y → pos (x + y) := sorry
lemma pos_mul {x y : ℝ} : pos x →  pos y → pos (x * y) := sorry

set_option blast.strategy "cc"

example (x y z w : ℝ)
  (x_pos : pos x) (y_pos : pos y) (z_pos : pos z) (w_pos : pos w) :
  x * y = z + w →  @safe_log (z + w) (pos_add z_pos w_pos) = @safe_log (x * y) (pos_mul x_pos y_pos) :=
by blast -- fails

end safe
