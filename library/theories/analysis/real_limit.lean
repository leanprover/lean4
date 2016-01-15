/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis

Instantiates the reals as a Banach space.
-/
import .metric_space data.real.complete data.set .normed_space
open real classical analysis nat
noncomputable theory

/- sup and inf -/

-- Expresses completeness, sup, and inf in a manner that is less constructive, but more convenient,
-- than the way it is done in data.real.complete.

-- Issue: real.sup and real.inf conflict with sup and inf in lattice.
-- Perhaps put algebra sup and inf into a namespace?

namespace real
open set

private definition exists_is_sup {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b)) :
  ∃ y, is_sup X y :=
let x := some (and.left H), b := some (and.right H) in
  exists_is_sup_of_inh_of_bdd X x (some_spec (and.left H)) b (some_spec (and.right H))

private definition sup_aux {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b)) :=
some (exists_is_sup H)

private definition sup_aux_spec {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b)) :
  is_sup X (sup_aux H) :=
some_spec (exists_is_sup H)

definition sup (X : set ℝ) : ℝ :=
if H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b) then sup_aux H else 0

proposition le_sup {x : ℝ} {X : set ℝ} (Hx : x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → x ≤ b) :
  x ≤ sup X :=
have H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b),
  from and.intro (exists.intro x Hx) (exists.intro b Hb),
by+ rewrite [↑sup, dif_pos H]; exact and.left (sup_aux_spec H) x Hx

proposition sup_le {X : set ℝ} (HX : ∃ x, x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → x ≤ b) :
  sup X ≤ b :=
have H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → x ≤ b),
  from and.intro HX (exists.intro b Hb),
by+ rewrite [↑sup, dif_pos H]; exact and.right (sup_aux_spec H) b Hb

proposition exists_mem_and_lt_of_lt_sup {X : set ℝ} (HX : ∃ x, x ∈ X) {b : ℝ} (Hb : b < sup X) :
∃ x, x ∈ X ∧ b < x :=
have ¬ ∀ x, x ∈ X → x ≤ b, from assume H, not_le_of_gt Hb (sup_le HX H),
obtain x (Hx : ¬ (x ∈ X → x ≤ b)), from exists_not_of_not_forall this,
exists.intro x
  (have x ∈ X ∧ ¬ x ≤ b, by rewrite [-not_implies_iff_and_not]; apply Hx,
     and.intro (and.left this) (lt_of_not_ge (and.right this)))

private definition exists_is_inf {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x)) :
  ∃ y, is_inf X y :=
let x := some (and.left H), b := some (and.right H) in
  exists_is_inf_of_inh_of_bdd X x (some_spec (and.left H)) b (some_spec (and.right H))

private definition inf_aux {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x)) :=
some (exists_is_inf H)

private definition inf_aux_spec {X : set ℝ} (H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x)) :
  is_inf X (inf_aux H) :=
some_spec (exists_is_inf H)

definition inf (X : set ℝ) : ℝ :=
if H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x) then inf_aux H else 0

proposition inf_le {x : ℝ} {X : set ℝ} (Hx : x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → b ≤ x) :
  inf X ≤ x :=
have H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x),
  from and.intro (exists.intro x Hx) (exists.intro b Hb),
by+ rewrite [↑inf, dif_pos H]; exact and.left (inf_aux_spec H) x Hx

proposition le_inf {X : set ℝ} (HX : ∃ x, x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → b ≤ x) :
  b ≤ inf X :=
have H : (∃ x, x ∈ X) ∧ (∃ b, ∀ x, x ∈ X → b ≤ x),
  from and.intro HX (exists.intro b Hb),
by+ rewrite [↑inf, dif_pos H]; exact and.right (inf_aux_spec H) b Hb

proposition exists_mem_and_lt_of_inf_lt {X : set ℝ} (HX : ∃ x, x ∈ X) {b : ℝ} (Hb : inf X < b) :
∃ x, x ∈ X ∧ x < b :=
have ¬ ∀ x, x ∈ X → b ≤ x, from assume H, not_le_of_gt Hb (le_inf HX H),
obtain x (Hx : ¬ (x ∈ X → b ≤ x)), from exists_not_of_not_forall this,
exists.intro x
  (have x ∈ X ∧ ¬ b ≤ x, by rewrite [-not_implies_iff_and_not]; apply Hx,
     and.intro (and.left this) (lt_of_not_ge (and.right this)))

section
local attribute mem [quasireducible]
-- TODO: is there a better place to put this?
proposition image_neg_eq (X : set ℝ) : (λ x, -x) ' X = {x | -x ∈ X} :=
set.ext (take x, iff.intro
  (assume H, obtain y [(Hy₁ : y ∈ X) (Hy₂ : -y = x)], from H,
    show -x ∈ X, by rewrite [-Hy₂, neg_neg]; exact Hy₁)
  (assume H : -x ∈ X, exists.intro (-x) (and.intro H !neg_neg)))

proposition sup_neg {X : set ℝ} (nonempty_X : ∃ x, x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → b ≤ x) :
  sup {x | -x ∈ X} = - inf X :=
let negX := {x | -x ∈ X} in
have nonempty_negX : ∃ x, x ∈ negX, from
  obtain x Hx, from nonempty_X,
  have -(-x) ∈ X,
    by rewrite neg_neg; apply Hx,
  exists.intro (-x) this,
have H₁ : ∀ x, x ∈ negX → x ≤ - inf X, from
  take x,
  assume H,
  have inf X ≤ -x,
    from inf_le H Hb,
  show x ≤ - inf X,
    from le_neg_of_le_neg this,
have H₂ : ∀ x, x ∈ X → -sup negX ≤ x, from
  take x,
  assume H,
  have -(-x) ∈ X, by rewrite neg_neg; apply H,
  have -x ≤ sup negX, from le_sup this H₁,
  show -sup negX ≤ x,
    from !neg_le_of_neg_le this,
eq_of_le_of_ge
  (show sup negX ≤ - inf X,
    from sup_le nonempty_negX H₁)
  (show -inf X ≤ sup negX,
    from !neg_le_of_neg_le (le_inf nonempty_X H₂))

proposition inf_neg {X : set ℝ} (nonempty_X : ∃ x, x ∈ X) {b : ℝ} (Hb : ∀ x, x ∈ X → x ≤ b) :
  inf {x | -x ∈ X} = - sup X :=
let negX := {x | -x ∈ X} in
have nonempty_negX : ∃ x, x ∈ negX, from
  obtain x Hx, from nonempty_X,
  have -(-x) ∈ X,
    by rewrite neg_neg; apply Hx,
  exists.intro (-x) this,
have Hb' : ∀ x, x ∈ negX → -b ≤ x,
  from take x, assume H, !neg_le_of_neg_le (Hb _ H),
have HX : X = {x | -x ∈ negX},
  from set.ext (take x, by rewrite [↑set_of, ↑mem, +neg_neg]),
show inf {x | -x ∈ X} = - sup X,
  using HX Hb' nonempty_negX, by rewrite [HX at {2}, sup_neg nonempty_negX Hb', neg_neg]
end
end real

/- the reals form a complete metric space -/

namespace analysis

theorem dist_eq_abs (x y : real) : dist x y = abs (x - y) := rfl

proposition converges_to_seq_real_intro {X : ℕ → ℝ} {y : ℝ}
    (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) < ε) :
  (X ⟶ y in ℕ) := H

proposition converges_to_seq_real_elim {X : ℕ → ℝ} {y : ℝ} (H : X ⟶ y in ℕ) :
    ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) < ε := H

proposition converges_to_seq_real_intro' {X : ℕ → ℝ} {y : ℝ}
    (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) ≤ ε) :
  converges_to_seq X y :=
converges_to_seq.intro H

open pnat subtype
local postfix ⁻¹ := pnat.inv

private definition pnat.succ (n : ℕ) : ℕ+ := tag (succ n) !succ_pos

private definition r_seq_of (X : ℕ → ℝ) : r_seq := λ n, X (elt_of n)

private lemma rate_of_cauchy_aux {X : ℕ → ℝ} (H : cauchy X) :
  ∀ k : ℕ+, ∃ N : ℕ+, ∀ m n : ℕ+,
    m ≥ N → n ≥ N → abs (X (elt_of m) - X (elt_of n)) ≤ of_rat k⁻¹ :=
take k : ℕ+,
have H1 : (k⁻¹ >[rat] (rat.of_num 0)), from !pnat.inv_pos,
have H2 : (of_rat k⁻¹ > of_rat (rat.of_num 0)), from !of_rat_lt_of_rat_of_lt H1,
obtain (N : ℕ) (H : ∀ m n, m ≥ N → n ≥ N → abs (X m - X n) < of_rat k⁻¹), from H _ H2,
exists.intro (pnat.succ N)
  (take m n : ℕ+,
    assume Hm : m ≥ (pnat.succ N),
    assume Hn : n ≥ (pnat.succ N),
    have Hm' : elt_of m ≥ N, begin apply le.trans, apply le_succ, apply Hm end,
    have Hn' : elt_of n ≥ N, begin apply le.trans, apply le_succ, apply Hn end,
    show abs (X (elt_of m) - X (elt_of n)) ≤ of_rat k⁻¹, from le_of_lt (H _ _ Hm' Hn'))

private definition rate_of_cauchy {X : ℕ → ℝ} (H : cauchy X) (k : ℕ+) : ℕ+ :=
some (rate_of_cauchy_aux H k)

private lemma cauchy_with_rate_of_cauchy {X : ℕ → ℝ} (H : cauchy X) :
  cauchy_with_rate (r_seq_of X) (rate_of_cauchy H) :=
take k : ℕ+,
some_spec (rate_of_cauchy_aux H k)

private lemma converges_to_with_rate_of_cauchy {X : ℕ → ℝ} (H : cauchy X) :
  ∃ l Nb, converges_to_with_rate (r_seq_of X) l Nb :=
begin
  apply exists.intro,
  apply exists.intro,
  apply converges_to_with_rate_of_cauchy_with_rate,
  exact cauchy_with_rate_of_cauchy H
end

theorem converges_seq_of_cauchy {X : ℕ → ℝ} (H : cauchy X) : converges_seq X :=
obtain l Nb (conv : converges_to_with_rate (r_seq_of X) l Nb),
  from converges_to_with_rate_of_cauchy H,
exists.intro l
  (take ε : ℝ,
    suppose ε > 0,
    obtain (k' : ℕ) (Hn : 1 / succ k' < ε), from archimedean_small `ε > 0`,
    let k : ℕ+ := tag (succ k') !succ_pos,
        N : ℕ+ := Nb k in
    have Hk : real.of_rat k⁻¹ < ε,
      by rewrite [↑pnat.inv, of_rat_divide]; exact Hn,
    exists.intro (elt_of N)
      (take n : ℕ,
        assume Hn : n ≥ elt_of N,
        let n' : ℕ+ := tag n (nat.lt_of_lt_of_le (has_property N) Hn) in
        have abs (X n - l) ≤ real.of_rat k⁻¹, by apply conv k n' Hn,
        show abs (X n - l) < ε, from lt_of_le_of_lt this Hk))

end analysis

definition complete_metric_space_real [reducible] [trans_instance] :
  complete_metric_space ℝ :=
⦃complete_metric_space, metric_space_real,
  complete := @analysis.converges_seq_of_cauchy
⦄

/- the real numbers can be viewed as a banach space -/

definition real_vector_space_real : real_vector_space ℝ :=
⦃ real_vector_space, real.discrete_linear_ordered_field,
  smul               := mul,
  smul_left_distrib  := left_distrib,
  smul_right_distrib := right_distrib,
  mul_smul           := mul.assoc,
  one_smul           := one_mul
⦄

definition banach_space_real [trans_instance] [reducible] : banach_space ℝ :=
⦃ banach_space, real_vector_space_real,
  norm                    := abs,
  norm_zero               := abs_zero,
  eq_zero_of_norm_eq_zero := λ a H, eq_zero_of_abs_eq_zero H,
  norm_triangle           := abs_add_le_abs_add_abs,
  norm_smul               := abs_mul,
  complete                := λ X H, analysis.complete ℝ H
⦄

/- limits under pointwise operations -/

section limit_operations
variables {X Y : ℕ → ℝ}
variables {x y : ℝ}

proposition mul_left_converges_to_seq (c : ℝ) (HX : X ⟶ x in ℕ) :
  (λ n, c * X n) ⟶ c * x in ℕ :=
smul_converges_to_seq c HX

proposition mul_right_converges_to_seq (c : ℝ) (HX : X ⟶ x in ℕ) :
  (λ n, X n * c) ⟶ x * c in ℕ :=
have (λ n, X n * c) = (λ n, c * X n), from funext (take x, !mul.comm),
by+ rewrite [this, mul.comm]; apply mul_left_converges_to_seq c HX

-- TODO: converges_to_seq_div, converges_to_seq_mul_left_iff, etc.

proposition abs_converges_to_seq_zero (HX : X ⟶ 0 in ℕ) : (λ n, abs (X n)) ⟶ 0 in ℕ :=
norm_converges_to_seq_zero HX

proposition converges_to_seq_zero_of_abs_converges_to_seq_zero (HX : (λ n, abs (X n)) ⟶ 0 in ℕ) :
  X ⟶ 0 in ℕ :=
converges_to_seq_zero_of_norm_converges_to_seq_zero HX

proposition abs_converges_to_seq_zero_iff (X : ℕ → ℝ) :
  ((λ n, abs (X n)) ⟶ 0 in ℕ) ↔ (X ⟶ 0 in ℕ) :=
iff.intro converges_to_seq_zero_of_abs_converges_to_seq_zero abs_converges_to_seq_zero

-- TODO: products of two sequences, converges_seq, limit_seq

end limit_operations

/- monotone sequences -/

section monotone_sequences
open real set
variable {X : ℕ → ℝ}

definition nondecreasing (X : ℕ → ℝ) : Prop := ∀ ⦃i j⦄, i ≤ j → X i ≤ X j

proposition nondecreasing_of_forall_le_succ (H : ∀ i, X i ≤ X (succ i)) : nondecreasing X :=
take i j, suppose i ≤ j,
have ∀ n, X i ≤ X (i + n), from
  take n, nat.induction_on n
    (by rewrite nat.add_zero; apply le.refl)
    (take n, assume ih, le.trans ih (H (i + n))),
have X i ≤ X (i + (j - i)), from !this,
by+ rewrite [add_sub_of_le `i ≤ j` at this]; exact this

proposition converges_to_seq_sup_of_nondecreasing (nondecX : nondecreasing X) {b : ℝ}
    (Hb : ∀ i, X i ≤ b) : X ⟶ sup (X ' univ) in ℕ :=
let sX := sup (X ' univ) in
have Xle : ∀ i, X i ≤ sX, from
  take i,
  have ∀ x, x ∈ X ' univ → x ≤ b, from
    (take x, assume H,
      obtain i [H' (Hi : X i = x)], from H,
      by rewrite -Hi; exact Hb i),
  show X i ≤ sX, from le_sup (mem_image_of_mem X !mem_univ) this,
have exX : ∃ x, x ∈ X ' univ,
  from exists.intro (X 0) (mem_image_of_mem X !mem_univ),
take ε, assume epos : ε > 0,
have sX - ε < sX, from !sub_lt_of_pos epos,
obtain x' [(H₁x' : x' ∈ X ' univ) (H₂x' : sX - ε < x')],
  from exists_mem_and_lt_of_lt_sup exX this,
obtain i [H' (Hi : X i = x')], from H₁x',
have Hi' : ∀ j, j ≥ i → sX - ε < X j, from
  take j, assume Hj, lt_of_lt_of_le (by rewrite Hi; apply H₂x') (nondecX Hj),
exists.intro i
  (take j, assume Hj : j ≥ i,
    have X j - sX ≤ 0, from sub_nonpos_of_le (Xle j),
    have eq₁ : abs (X j - sX) = sX - X j, using this, by rewrite [abs_of_nonpos this, neg_sub],
    have sX - ε < X j, from lt_of_lt_of_le (by rewrite Hi; apply H₂x') (nondecX Hj),
    have sX < X j + ε, from lt_add_of_sub_lt_right this,
    have sX - X j < ε, from sub_lt_left_of_lt_add this,
    show (abs (X j - sX)) < ε, using eq₁ this, by rewrite eq₁; exact this)

definition nonincreasing (X : ℕ → ℝ) : Prop := ∀ ⦃i j⦄, i ≤ j → X i ≥ X j

proposition nodecreasing_of_nonincreasing_neg (nonincX : nonincreasing (λ n, - X n)) :
  nondecreasing (λ n, X n) :=
take i j, suppose i ≤ j,
show X i ≤ X j, from le_of_neg_le_neg (nonincX this)

proposition noincreasing_neg_of_nondecreasing (nondecX : nondecreasing X) :
  nonincreasing (λ n, - X n) :=
take i j, suppose i ≤ j,
show - X i ≥ - X j, from neg_le_neg (nondecX this)

proposition nonincreasing_neg_iff (X : ℕ → ℝ) : nonincreasing (λ n, - X n) ↔ nondecreasing X :=
iff.intro nodecreasing_of_nonincreasing_neg noincreasing_neg_of_nondecreasing

proposition nonincreasing_of_nondecreasing_neg (nondecX : nondecreasing (λ n, - X n)) :
  nonincreasing (λ n, X n) :=
take i j, suppose i ≤ j,
show X i ≥ X j, from le_of_neg_le_neg (nondecX this)

proposition nodecreasing_neg_of_nonincreasing (nonincX : nonincreasing X) :
  nondecreasing (λ n, - X n) :=
take i j, suppose i ≤ j,
show - X i ≤ - X j, from neg_le_neg (nonincX this)

proposition nondecreasing_neg_iff (X : ℕ → ℝ) : nondecreasing (λ n, - X n) ↔ nonincreasing X :=
iff.intro nonincreasing_of_nondecreasing_neg nodecreasing_neg_of_nonincreasing

proposition nonincreasing_of_forall_succ_le (H : ∀ i, X (succ i) ≤ X i) : nonincreasing X :=
begin
  rewrite -nondecreasing_neg_iff,
  show nondecreasing (λ n : ℕ, - X n), from
    nondecreasing_of_forall_le_succ (take i, neg_le_neg (H i))
end

proposition converges_to_seq_inf_of_nonincreasing (nonincX : nonincreasing X) {b : ℝ}
    (Hb : ∀ i, b ≤ X i) : X ⟶ inf (X ' univ) in ℕ :=
have H₁ : ∃ x, x ∈ X ' univ, from exists.intro (X 0) (mem_image_of_mem X !mem_univ),
have H₂ : ∀ x, x ∈ X ' univ → b ≤ x, from
  (take x, assume H,
    obtain i [Hi₁ (Hi₂ : X i = x)], from H,
    show b ≤ x, by rewrite -Hi₂; apply Hb i),
have H₃ : {x : ℝ | -x ∈ X ' univ} = {x : ℝ | x ∈ (λ n, -X n) ' univ}, from calc
  {x : ℝ | -x ∈ X ' univ} = (λ y, -y) ' (X ' univ) : by rewrite image_neg_eq
                       ... = {x : ℝ | x ∈ (λ n, -X n) ' univ} : image_compose,
have H₄ : ∀ i, - X i ≤ - b, from take i, neg_le_neg (Hb i),
begin+
  -- need krewrite here
  krewrite [-neg_converges_to_seq_iff, -sup_neg H₁ H₂, H₃, -nondecreasing_neg_iff at nonincX],
  apply converges_to_seq_sup_of_nondecreasing nonincX H₄
end

end monotone_sequences

/- x^n converges to 0 if abs x < 1 -/

section xn
open nat set

theorem pow_converges_to_seq_zero {x : ℝ} (H : abs x < 1) :
  (λ n, x^n) ⟶ 0 in ℕ :=
suffices H' : (λ n, (abs x)^n) ⟶ 0 in ℕ, from
  have (λ n, (abs x)^n) = (λ n, abs (x^n)), from funext (take n, eq.symm !abs_pow),
  using this,
    by rewrite this at H'; exact converges_to_seq_zero_of_abs_converges_to_seq_zero H',
let  aX := (λ n, (abs x)^n),
    iaX := real.inf (aX ' univ),
    asX := (λ n, (abs x)^(succ n)) in
have noninc_aX : nonincreasing aX, from
  nonincreasing_of_forall_succ_le
    (take i,
      assert (abs x) * (abs x)^i ≤ 1 * (abs x)^i,
        from mul_le_mul_of_nonneg_right (le_of_lt H) (!pow_nonneg_of_nonneg !abs_nonneg),
      assert (abs x) * (abs x)^i ≤ (abs x)^i, by krewrite one_mul at this; exact this,
      show (abs x) ^ (succ i) ≤ (abs x)^i, by rewrite pow_succ; apply this),
have bdd_aX : ∀ i, 0 ≤ aX i, from take i, !pow_nonneg_of_nonneg !abs_nonneg,
assert aXconv : aX ⟶ iaX in ℕ, proof converges_to_seq_inf_of_nonincreasing noninc_aX bdd_aX qed,
have asXconv : asX ⟶ iaX in ℕ, from converges_to_seq_offset_succ aXconv,
have asXconv' : asX ⟶ (abs x) * iaX in ℕ, from mul_left_converges_to_seq (abs x) aXconv,
have iaX = (abs x) * iaX, from converges_to_seq_unique asXconv asXconv',
assert iaX = 0, from eq_zero_of_mul_eq_self_left (ne_of_lt H) (eq.symm this),
show aX ⟶ 0 in ℕ, begin rewrite -this, exact aXconv end --from this ▸ aXconv

end xn

/- continuity on the reals -/

section continuous

theorem continuous_real_elim {f : ℝ → ℝ} (H : continuous f) :
  ∀ x : ℝ, ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ,
    abs (x' - x) < δ → abs (f x' - f x) < ε :=
H

theorem continuous_real_intro {f : ℝ → ℝ}
  (H : ∀ x : ℝ, ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ,
    abs (x' - x) < δ → abs (f x' - f x) < ε) :
  continuous f :=
H

theorem pos_on_nbhd_of_cts_of_pos {f : ℝ → ℝ} (Hf : continuous f) {b : ℝ} (Hb : f b > 0) :
                ∃ δ : ℝ, δ > 0 ∧ ∀ y, abs (y - b) < δ → f y > 0 :=
  begin
    let Hcont := continuous_real_elim Hf b Hb,
    cases Hcont with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro y Hy,
    let Hy' := and.right Hδ y Hy,
    note Hlt := sub_lt_of_abs_sub_lt_left Hy',
    rewrite sub_self at Hlt,
    assumption
  end

theorem neg_on_nbhd_of_cts_of_neg {f : ℝ → ℝ} (Hf : continuous f) {b : ℝ} (Hb : f b < 0) :
                ∃ δ : ℝ, δ > 0 ∧ ∀ y, abs (y - b) < δ → f y < 0 :=
  begin
    let Hcont := continuous_real_elim Hf b (neg_pos_of_neg Hb),
    cases Hcont with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro y Hy,
    let Hy' := and.right Hδ y Hy,
    let Hlt := sub_lt_of_abs_sub_lt_right Hy',
    note Hlt' := lt_add_of_sub_lt_left Hlt,
    rewrite [add.comm at Hlt', -sub_eq_add_neg at Hlt', sub_self at Hlt'],
    assumption
  end

theorem continuous_neg_of_continuous {f : ℝ → ℝ} (Hcon : continuous f) : continuous (λ x, - f x) :=
  begin
    apply continuous_real_intro,
    intros x ε Hε,
    cases continuous_real_elim Hcon x Hε with δ Hδ,
    cases Hδ with Hδ₁ Hδ₂,
    existsi δ,
    split,
    assumption,
    intros x' Hx',
    let HD := Hδ₂ x' Hx',
    rewrite [-abs_neg, neg_neg_sub_neg],
    exact HD
  end

theorem continuous_offset_of_continuous {f : ℝ → ℝ} (Hcon : continuous f) (a : ℝ) :
        continuous (λ x, (f x) + a) :=
  begin
    apply continuous_real_intro,
    intros x ε Hε,
    cases continuous_real_elim Hcon x Hε with δ Hδ,
    cases Hδ with Hδ₁ Hδ₂,
    existsi δ,
    split,
    assumption,
    intros x' Hx',
    rewrite [add_sub_comm, sub_self, add_zero],
    apply Hδ₂,
    assumption
  end

end continuous

/-
proposition converges_to_at_unique {f : M → N} {y₁ y₂ : N} {x : M}
  (H₁ : f ⟶ y₁ '[at x]) (H₂ : f ⟶ y₂ '[at x]) : y₁ = y₂ :=
eq_of_forall_dist_le
  (take ε, suppose ε > 0,
    have e2pos : ε / 2 > 0, from  div_pos_of_pos_of_pos `ε > 0` two_pos,
    obtain δ₁ [(δ₁pos : δ₁ > 0) (Hδ₁ : ∀ x', x ≠ x' ∧ dist x x' < δ₁ → dist (f x') y₁ < ε / 2)],
      from H₁ e2pos,
    obtain δ₂ [(δ₂pos : δ₂ > 0) (Hδ₂ : ∀ x', x ≠ x' ∧ dist x x' < δ₂ → dist (f x') y₂ < ε / 2)],
      from H₂ e2pos,
    let δ := min δ₁ δ₂ in
    have δ > 0, from lt_min δ₁pos δ₂pos,
-/
