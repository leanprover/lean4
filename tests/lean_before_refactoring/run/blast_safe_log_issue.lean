import data.real
open real

namespace safe

definition pos (x : ℝ) := x > 0

constants (exp : ℝ → ℝ)
constants (safe_log : Π (x : ℝ), pos x → ℝ)

lemma pos_add {x y : ℝ} : pos x →  pos y → pos (x + y) := sorry
lemma pos_mul {x y : ℝ} : pos x →  pos y → pos (x * y) := sorry
lemma log_mul [simp] : ∀ (x y : ℝ) (x_pos : pos x) (y_pos : pos y), safe_log (x * y) (pos_mul x_pos y_pos)  = safe_log x x_pos + safe_log y y_pos := sorry

example (x y z w : ℝ)
  (x_pos : pos x) (y_pos : pos y) (z_pos : pos z) (w_pos : pos w) :
  x * y = z + w → safe_log (z + w) (pos_add z_pos w_pos) = safe_log x x_pos + safe_log y y_pos :=
by inst_simp

end safe
