import data.real
open real


namespace safe

definition pos (x : ℝ) := x > 0
definition nzero (x : ℝ) := x ≠ 0

constants (exp : ℝ → ℝ)
constants (safe_log : Π (x : ℝ), pos x → ℝ)
constants (safe_inv : Π (x : ℝ), nzero x → ℝ)

notation `log`:max x:max := (@safe_log x (by grind))
notation [priority 100000] x:max ⁻¹ := (@safe_inv x (by grind))

definition sq (x : ℝ) := x * x

notation a `²` := sq a

lemma nzero_of_pos [intro!] {x : ℝ} : pos x → nzero x := sorry

lemma pos_bit1 [intro!] {x : ℝ} : pos x → pos (: bit1 x :) := sorry
lemma pos_bit0 [intro!] {x : ℝ} : pos x → pos (: bit0 x :) := sorry
lemma pos_inv [forward] {x : ℝ} : pos x → (: pos (inv x) :) := sorry
lemma pos_1 [intro!] : pos (1:ℝ) := sorry
lemma pos_add [intro!] [forward] {x y : ℝ} : pos x →  pos y → pos (: x + y :) := sorry
lemma pos_mul [intro!] [forward] {x y : ℝ} : pos x →  pos y → pos (: x * y :) := sorry
lemma pos_sq [intro!]  {x : ℝ} : pos x → pos (: sq x :) := sorry
lemma inv_pos [intro!] {x : ℝ} : pos x → pos (: x⁻¹ :) := sorry
lemma exp_pos [intro!] (x : ℝ) : pos (: exp x :) := sorry
lemma log_mul [forward] : ∀ (x y : ℝ), pos x →  pos y → (: log (x * y) :) = (: log x + log y :) := sorry
lemma log_sq [forward] : ∀ (x : ℝ), pos x → (: log (sq x) :) = (: 2 * log x :) := sorry
lemma log_inv [forward] : ∀ (x : ℝ), pos x →  (: log (x⁻¹) :) = (: - log x :) := sorry
lemma inv_mul [forward] : ∀ (x y : ℝ), pos x → pos y → (: (x * y)⁻¹ :) = (: x⁻¹ * y⁻¹ :) := sorry
lemma exp_add [forward] : ∀ (x y : ℝ), (: exp (x + y) :) = (: exp x * exp y :) := sorry
lemma pair_prod [forward] : ∀ (x y : ℝ), (: sq x + 2 * x * y + sq y :) = sq (x + y) := sorry
lemma mul_two_sum [forward] : ∀ (x : ℝ), (: 2 * x :) = (: x + x :) := sorry
lemma sub_def [forward] : ∀ (x y : ℝ), (x - y) = x + -y := sorry
lemma mul_div_cancel [forward] : ∀ (x y : ℝ), (y * x) / y = x := sorry
lemma div_neg [forward] : ∀ (x y : ℝ), x / -y = - (x / y) := sorry


attribute right_distrib [forward]
attribute left_distrib [forward]

set_option blast.strategy "ematch"

example (x y z w : ℝ) : pos x → pos y → pos z → pos w → x * y = w + exp z →
log ((w² + 2 * w * exp z + (exp z)²)) / -2 = log (x⁻¹) - log y :=
by blast

end safe
