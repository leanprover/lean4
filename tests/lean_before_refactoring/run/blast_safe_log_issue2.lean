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

attribute [intro!]
lemma nzero_of_pos {x : ℝ} : pos x → nzero x := sorry

attribute [intro!]
lemma pos_bit1 {x : ℝ} : pos x → pos (: bit1 x :) := sorry
attribute [intro!]
lemma pos_bit0 {x : ℝ} : pos x → pos (: bit0 x :) := sorry
attribute [forward]
lemma pos_inv {x : ℝ} : pos x → (: pos (inv x) :) := sorry
attribute [intro!]
lemma pos_1 : pos (1:ℝ) := sorry
attribute [intro!, forward]
lemma pos_add {x y : ℝ} : pos x →  pos y → pos (: x + y :) := sorry
attribute [intro!, forward]
lemma pos_mul {x y : ℝ} : pos x →  pos y → pos (: x * y :) := sorry
attribute [intro!]
lemma pos_sq {x : ℝ} : pos x → pos (: sq x :) := sorry
attribute [intro!]
lemma inv_pos {x : ℝ} : pos x → pos (: x⁻¹ :) := sorry
attribute [intro!]
lemma exp_pos (x : ℝ) : pos (: exp x :) := sorry
attribute [forward]
lemma log_mul : ∀ (x y : ℝ), pos x →  pos y → (: log (x * y) :) = (: log x + log y :) := sorry
attribute [forward]
lemma log_sq : ∀ (x : ℝ), pos x → (: log (sq x) :) = (: 2 * log x :) := sorry
attribute [forward]
lemma log_inv : ∀ (x : ℝ), pos x →  (: log (x⁻¹) :) = (: - log x :) := sorry
attribute [forward]
lemma inv_mul : ∀ (x y : ℝ), pos x → pos y → (: (x * y)⁻¹ :) = (: x⁻¹ * y⁻¹ :) := sorry
attribute [forward]
lemma exp_add : ∀ (x y : ℝ), (: exp (x + y) :) = (: exp x * exp y :) := sorry
attribute [forward]
lemma pair_prod : ∀ (x y : ℝ), (: sq x + 2 * x * y + sq y :) = sq (x + y) := sorry
attribute [forward]
lemma mul_two_sum : ∀ (x : ℝ), (: 2 * x :) = (: x + x :) := sorry
attribute [forward]
lemma sub_def : ∀ (x y : ℝ), (x - y) = x + -y := sorry
attribute [forward]
lemma mul_div_cancel : ∀ (x y : ℝ), (y * x) / y = x := sorry
attribute [forward]
lemma div_neg : ∀ (x y : ℝ), x / -y = - (x / y) := sorry


attribute right_distrib [forward]
attribute left_distrib [forward]

set_option blast.strategy "ematch"

example (x y z w : ℝ) : pos x → pos y → pos z → pos w → x * y = w + exp z →
log ((w² + 2 * w * exp z + (exp z)²)) / -2 = log (x⁻¹) - log y :=
by blast

end safe
