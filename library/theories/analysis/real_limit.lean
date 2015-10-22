/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis

Instantiates the reals as a metric space, and expresses completeness, sup, and inf in
a manner that is less constructive, but more convenient, than the way it is done in
data.real.complete.

The definitions here are noncomputable, for various reasons:

(1) We rely on the nonconstructive definition of abs.
(2) The theory of the reals uses the "some" operator e.g. to define the ceiling function.
    This can't be defined constructively as an operation on the quotient, because
    such a function is not continuous.
(3) We use "forall" and "exists" to say that a series converges, rather than carrying
    around rates of convergence explicitly. We then use "some" whenever we need to extract
    information, such as the limit.

These could be avoided in a constructive theory of analysis, but here we will not
follow that route.
-/
import .metric_space data.real.complete
open real classical algebra
noncomputable theory

namespace real
local postfix ⁻¹ := pnat.inv
/- the reals form a metric space -/

protected definition to_metric_space [instance] : metric_space ℝ :=
⦃ metric_space,
  dist               := λ x y, abs (x - y),
  dist_self          := λ x, abstract by rewrite [sub_self, abs_zero] end,
  eq_of_dist_eq_zero := λ x y, algebra.eq_of_abs_sub_eq_zero,
  dist_comm          := abs_sub,
  dist_triangle      := abs_sub_le
⦄

open nat
open [classes] rat

definition converges_to_seq (X : ℕ → ℝ) (y : ℝ) : Prop :=
∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) < ε

proposition converges_to_seq.intro {X : ℕ → ℝ} {y : ℝ}
    (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → abs (X n - y) ≤ ε) :
  converges_to_seq X y :=
metric_space.converges_to_seq.intro H

notation X `⟶` y `in` `ℕ` := converges_to_seq X y

definition converges_seq [class] (X : ℕ → ℝ) : Prop := ∃ y, X ⟶ y in ℕ

definition limit_seq (X : ℕ → ℝ) [H : converges_seq X] : ℝ := some H

proposition converges_to_limit_seq (X : ℕ → ℝ) [H : converges_seq X] :
  (X ⟶ limit_seq X in ℕ) :=
some_spec H

proposition converges_to_seq_unique {X : ℕ → ℝ} {y₁ y₂ : ℝ}
  (H₁ : X ⟶ y₁ in ℕ) (H₂ : X ⟶ y₂ in ℕ) : y₁ = y₂ :=
metric_space.converges_to_seq_unique H₁ H₂

proposition eq_limit_of_converges_to_seq {X : ℕ → ℝ} (y : ℝ) (H : X ⟶ y in ℕ) :
  y = @limit_seq X (exists.intro y H) :=
converges_to_seq_unique H (@converges_to_limit_seq X (exists.intro y H))

proposition converges_to_seq_constant (y : ℝ) : (λn, y) ⟶ y in ℕ :=
metric_space.converges_to_seq_constant y

proposition converges_to_seq_offset {X : ℕ → ℝ} {y : ℝ} (k : ℕ) (H : X ⟶ y in ℕ) :
  (λ n, X (n + k)) ⟶ y in ℕ :=
metric_space.converges_to_seq_offset k H

proposition converges_to_seq_offset_left {X : ℕ → ℝ} {y : ℝ} (k : ℕ) (H : X ⟶ y in ℕ) :
  (λ n, X (k + n)) ⟶ y in ℕ :=
metric_space.converges_to_seq_offset_left k H

proposition converges_to_set_offset_succ {X : ℕ → ℝ} {y : ℝ} (H : X ⟶ y in ℕ) :
  (λ n, X (succ n)) ⟶ y in ℕ :=
metric_space.converges_to_seq_offset_succ H

proposition converges_to_seq_of_converges_to_seq_offset
    {X : ℕ → ℝ} {y : ℝ} {k : ℕ} (H : (λ n, X (n + k)) ⟶ y in ℕ) :
  X ⟶ y in ℕ :=
metric_space.converges_to_seq_of_converges_to_seq_offset H

proposition converges_to_seq_of_converges_to_seq_offset_left
    {X : ℕ → ℝ} {y : ℝ} {k : ℕ} (H : (λ n, X (k + n)) ⟶ y in ℕ) :
  X ⟶ y in ℕ :=
metric_space.converges_to_seq_of_converges_to_seq_offset_left H

proposition converges_to_seq_of_converges_to_seq_offset_succ
    {X : ℕ → ℝ} {y : ℝ} (H : (λ n, X (succ n)) ⟶ y in ℕ) :
  X ⟶ y in ℕ :=
metric_space.converges_to_seq_of_converges_to_seq_offset_succ H

proposition converges_to_seq_offset_iff (X : ℕ → ℝ) (y : ℝ) (k : ℕ) :
  ((λ n, X (n + k)) ⟶ y in ℕ) ↔ (X ⟶ y in ℕ) :=
metric_space.converges_to_seq_offset_iff X y k

proposition converges_to_seq_offset_left_iff (X : ℕ → ℝ) (y : ℝ) (k : ℕ) :
  ((λ n, X (k + n)) ⟶ y in ℕ) ↔ (X ⟶ y in ℕ) :=
metric_space.converges_to_seq_offset_left_iff X y k

proposition converges_to_seq_offset_succ_iff (X : ℕ → ℝ) (y : ℝ) :
  ((λ n, X (succ n)) ⟶ y in ℕ) ↔ (X ⟶ y in ℕ) :=
metric_space.converges_to_seq_offset_succ_iff X y

/- the completeness of the reals, "translated" from data.real.complete -/

definition cauchy (X : ℕ → ℝ) := metric_space.cauchy X

section
  open pnat subtype

  private definition pnat.succ (n : ℕ) : ℕ+ := tag (succ n) !succ_pos

  private definition r_seq_of (X : ℕ → ℝ) : r_seq := λ n, X (elt_of n)

  private lemma rate_of_cauchy_aux {X : ℕ → ℝ} (H : cauchy X) :
    ∀ k : ℕ+, ∃ N : ℕ+, ∀ m n : ℕ+,
      m ≥ N → n ≥ N → abs (X (elt_of m) - X (elt_of n)) ≤ of_rat k⁻¹ :=
  take k : ℕ+,
  have H1 : (k⁻¹ > (rat.of_num 0)), from !inv_pos,
  have H2 : (of_rat k⁻¹ > of_rat (rat.of_num 0)), from !of_rat_lt_of_rat_of_lt H1,
  obtain (N : ℕ) (H : ∀ m n, m ≥ N → n ≥ N → abs (X m - X n) < of_rat k⁻¹), from H _ H2,
  exists.intro (pnat.succ N)
    (take m n : ℕ+,
      assume Hm : m ≥ (pnat.succ N),
      assume Hn : n ≥ (pnat.succ N),
      have Hm' : elt_of m ≥ N, begin apply algebra.le.trans, apply le_succ, apply Hm end,
      have Hn' : elt_of n ≥ N, begin apply algebra.le.trans, apply le_succ, apply Hn end,
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
proposition image_neg_eq (X : set ℝ) : (λ x, -x) '[X] = {x | -x ∈ X} :=
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
end

/- limits under pointwise operations -/

section limit_operations
open nat

variables {X Y : ℕ → ℝ}
variables {x y : ℝ}

proposition add_converges_to_seq (HX : X ⟶ x in ℕ) (HY : Y ⟶ y in ℕ) :
  (λ n, X n + Y n) ⟶ x + y in ℕ :=
take ε, suppose ε > 0,
have e2pos : ε / 2 > 0, from  div_pos_of_pos_of_pos `ε > 0` two_pos,
obtain N₁ (HN₁ : ∀ {n}, n ≥ N₁ → abs (X n - x) < ε / 2), from HX e2pos,
obtain N₂ (HN₂ : ∀ {n}, n ≥ N₂ → abs (Y n - y) < ε / 2), from HY e2pos,
let N := max N₁ N₂ in
exists.intro N
  (take n,
    suppose n ≥ N,
    have ngtN₁ : n ≥ N₁, from nat.le_trans !le_max_left `n ≥ N`,
    have ngtN₂ : n ≥ N₂, from nat.le_trans !le_max_right `n ≥ N`,
    show abs ((X n + Y n) - (x + y)) < ε, from calc
      abs ((X n + Y n) - (x + y))
            = abs ((X n - x) + (Y n - y))   : by rewrite [sub_add_eq_sub_sub, *sub_eq_add_neg,
                                                         *add.assoc, add.left_comm (-x)]
        ... ≤ abs (X n - x) + abs (Y n - y) : abs_add_le_abs_add_abs
        ... < ε / 2 + ε / 2                 : add_lt_add (HN₁ ngtN₁) (HN₂ ngtN₂)
        ... = ε                             : add_halves)

private lemma mul_left_converges_to_seq_of_pos {c : ℝ} (cnz : c ≠ 0) (HX : X ⟶ x in ℕ) :
  (λ n, c * X n) ⟶ c * x in ℕ :=
take ε, suppose ε > 0,
have abscpos : abs c > 0, from abs_pos_of_ne_zero cnz,
have epos : ε / abs c > 0, from  div_pos_of_pos_of_pos `ε > 0` abscpos,
obtain N (HN : ∀ {n}, n ≥ N → abs (X n - x) < ε / abs c), from HX epos,
exists.intro N
  (take n,
    suppose n ≥ N,
    have H : abs (X n - x) < ε / abs c, from HN this,
    show abs (c * X n - c * x) < ε, from calc
      abs (c * X n - c * x) = abs c * abs (X n - x) : by rewrite [-mul_sub_left_distrib, abs_mul]
                        ... < abs c * (ε / abs c)   : mul_lt_mul_of_pos_left H abscpos
                        ... = ε                     : mul_div_cancel' (ne_of_gt abscpos))

proposition mul_left_converges_to_seq (c : ℝ) (HX : X ⟶ x in ℕ) :
  (λ n, c * X n) ⟶ c * x in ℕ :=
by_cases
  (assume cz : c = 0,
    have (λ n, c * X n) = (λ n, 0), from funext (take x, by rewrite [cz, zero_mul]),
    by+ rewrite [this, cz, zero_mul]; apply converges_to_seq_constant)
  (suppose c ≠ 0, mul_left_converges_to_seq_of_pos this HX)

proposition mul_right_converges_to_seq (c : ℝ) (HX : X ⟶ x in ℕ) :
  (λ n, X n * c) ⟶ x * c in ℕ :=
have (λ n, X n * c) = (λ n, c * X n), from funext (take x, !mul.comm),
by+ rewrite [this, mul.comm]; apply mul_left_converges_to_seq c HX

-- TODO: converges_to_seq_div, converges_to_seq_mul_left_iff, etc.

proposition neg_converges_to_seq (HX : X ⟶ x in ℕ) :
  (λ n, - X n) ⟶ - x in ℕ :=
take ε, suppose ε > 0,
obtain N (HN : ∀ {n}, n ≥ N → abs (X n - x) < ε), from HX this,
exists.intro N
  (take n,
    suppose n ≥ N,
    show abs (- X n - (- x)) < ε,
      by rewrite [-neg_neg_sub_neg, *neg_neg, abs_neg]; exact HN `n ≥ N`)

proposition neg_converges_to_seq_iff (X : ℕ → ℝ) :
  ((λ n, - X n) ⟶ - x in ℕ) ↔ (X ⟶ x in ℕ) :=
have aux : X = λ n, (- (- X n)), from funext (take n, by rewrite neg_neg),
iff.intro
  (assume H : (λ n, -X n)⟶ -x in ℕ,
    show X ⟶ x in ℕ, by+ rewrite [aux, -neg_neg x]; exact neg_converges_to_seq H)
  neg_converges_to_seq

proposition abs_converges_to_seq_zero (HX : X ⟶ 0 in ℕ) : (λ n, abs (X n)) ⟶ 0 in ℕ :=
take ε, suppose ε > 0,
obtain N (HN : ∀ n, n ≥ N → abs (X n - 0) < ε), from HX `ε > 0`,
exists.intro N
  (take n, assume Hn : n ≥ N,
    have abs (X n) < ε, begin rewrite -(sub_zero (X n)), apply HN n Hn end,
    show abs (abs (X n) - 0) < ε, using this,
      by rewrite [sub_zero, abs_of_nonneg !abs_nonneg]; apply this)

proposition converges_to_seq_zero_of_abs_converges_to_seq_zero (HX : (λ n, abs (X n)) ⟶ 0 in ℕ) :
  X ⟶ 0 in ℕ :=
take ε, suppose ε > 0,
obtain N (HN : ∀ n, n ≥ N → abs (abs (X n) - 0) < ε), from HX `ε > 0`,
exists.intro (N : ℕ)
  (take n : ℕ, assume Hn : n ≥ N,
    have HN' : abs (abs (X n) - 0) < ε, from HN n Hn,
    have abs (X n) < ε,
      by+ rewrite [sub_zero at HN', abs_of_nonneg !abs_nonneg at HN']; apply HN',
    show abs (X n - 0) < ε, using this,
      by rewrite sub_zero; apply this)

proposition abs_converges_to_seq_zero_iff (X : ℕ → ℝ) :
  ((λ n, abs (X n)) ⟶ 0 in ℕ) ↔ (X ⟶ 0 in ℕ) :=
iff.intro converges_to_seq_zero_of_abs_converges_to_seq_zero abs_converges_to_seq_zero

-- TODO: products of two sequences, converges_seq, limit_seq

end limit_operations

/- monotone sequences -/

section monotone_sequences
open nat set

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
    (Hb : ∀ i, X i ≤ b) : X ⟶ sup (X '[univ]) in ℕ :=
let sX := sup (X '[univ]) in
have Xle : ∀ i, X i ≤ sX, from
  take i,
  have ∀ x, x ∈ X '[univ] → x ≤ b, from
    (take x, assume H,
      obtain i [H' (Hi : X i = x)], from H,
      by rewrite -Hi; exact Hb i),
  show X i ≤ sX, from le_sup (mem_image_of_mem X !mem_univ) this,
have exX : ∃ x, x ∈ X '[univ],
  from exists.intro (X 0) (mem_image_of_mem X !mem_univ),
take ε, assume epos : ε > 0,
have sX - ε < sX, from !sub_lt_of_pos epos,
obtain x' [(H₁x' : x' ∈ X '[univ]) (H₂x' : sX - ε < x')],
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
    (Hb : ∀ i, b ≤ X i) : X ⟶ inf (X '[univ]) in ℕ :=
have H₁ : ∃ x, x ∈ X '[univ], from exists.intro (X 0) (mem_image_of_mem X !mem_univ),
have H₂ : ∀ x, x ∈ X '[univ] → b ≤ x, from
  (take x, assume H,
    obtain i [Hi₁ (Hi₂ : X i = x)], from H,
    show b ≤ x, by rewrite -Hi₂; apply Hb i),
have H₃ : {x : ℝ | -x ∈ X '[univ]} = {x : ℝ | x ∈ (λ n, -X n) '[univ]}, from calc
  {x : ℝ | -x ∈ X '[univ]} = (λ y, -y) '[X '[univ]] : by rewrite image_neg_eq
                       ... = {x : ℝ | x ∈ (λ n, -X n) '[univ]} : image_compose,
have H₄ : ∀ i, - X i ≤ - b, from take i, neg_le_neg (Hb i),
begin+
  rewrite [-neg_converges_to_seq_iff, -sup_neg H₁ H₂, H₃, -nondecreasing_neg_iff at nonincX],
  apply converges_to_seq_sup_of_nondecreasing nonincX H₄
end

end monotone_sequences

section xn
open nat set

theorem pow_converges_to_seq_zero {x : ℝ} (H : abs x < 1) :
  (λ n, x^n) ⟶ 0 in ℕ :=
suffices H' : (λ n, (abs x)^n) ⟶ 0 in ℕ, from
  have (λ n, (abs x)^n) = (λ n, abs (x^n)), from funext (take n, eq.symm !abs_pow),
  using this,
    by rewrite this at H'; exact converges_to_seq_zero_of_abs_converges_to_seq_zero H',
let  aX := (λ n, (abs x)^n),
    iaX := inf (aX '[univ]),
    asX := (λ n, (abs x)^(succ n)) in
have noninc_aX : nonincreasing aX, from
  nonincreasing_of_forall_succ_le
    (take i,
      assert (abs x) * (abs x)^i ≤ 1 * (abs x)^i,
        from mul_le_mul_of_nonneg_right (le_of_lt H) (!pow_nonneg_of_nonneg !abs_nonneg),
      assert (abs x) * (abs x)^i ≤ (abs x)^i, by krewrite one_mul at this; exact this,
      show (abs x) ^ (succ i) ≤ (abs x)^i, by rewrite pow_succ; apply this),
have bdd_aX : ∀ i, 0 ≤ aX i, from take i, !pow_nonneg_of_nonneg !abs_nonneg,
assert aXconv : aX ⟶ iaX in ℕ, from converges_to_seq_inf_of_nonincreasing noninc_aX bdd_aX,
have asXconv : asX ⟶ iaX in ℕ, from metric_space.converges_to_seq_offset_succ aXconv,
have asXconv' : asX ⟶ (abs x) * iaX in ℕ, from mul_left_converges_to_seq (abs x) aXconv,
have iaX = (abs x) * iaX, from converges_to_seq_unique asXconv asXconv',
assert iaX = 0, from eq_zero_of_mul_eq_self_left (ne_of_lt H) (eq.symm this),
show aX ⟶ 0 in ℕ, begin rewrite -this, exact aXconv end --from this ▸ aXconv

end xn

section continuous

-- this definition should be inherited from metric_space once a migrate is done.
definition continuous (f : ℝ → ℝ) :=
  ∀ x : ℝ, ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x' : ℝ, abs (x - x') < δ → abs (f x - f x') < ε

theorem pos_on_nbhd_of_cts_of_pos {f : ℝ → ℝ} (Hf : continuous f) {b : ℝ} (Hb : f b > 0) :
                ∃ δ : ℝ, δ > 0 ∧ ∀ y, abs (b - y) < δ → f y > 0 :=
  begin
    let Hcont := Hf b Hb,
    cases Hcont with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro y Hy,
    let Hy' := and.right Hδ y Hy,
    let Hlt := sub_lt_of_abs_sub_lt_right Hy',
    rewrite sub_self at Hlt,
    assumption
  end

theorem neg_on_nbhd_of_cts_of_neg {f : ℝ → ℝ} (Hf : continuous f) {b : ℝ} (Hb : f b < 0) :
                ∃ δ : ℝ, δ > 0 ∧ ∀ y, abs (b - y) < δ → f y < 0 :=
  begin
    let Hcont := Hf b (neg_pos_of_neg Hb),
    cases Hcont with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intro y Hy,
    let Hy' := and.right Hδ y Hy,
    let Hlt := sub_lt_of_abs_sub_lt_left Hy',
    let Hlt' := lt_add_of_sub_lt_right Hlt,
    rewrite [-sub_eq_add_neg at Hlt', sub_self at Hlt'],
    assumption
  end

theorem neg_continuous_of_continuous {f : ℝ → ℝ} (Hcon : continuous f) : continuous (λ x, - f x) :=
  begin
    intros x ε Hε,
    cases Hcon x Hε with δ Hδ,
    cases Hδ with Hδ₁ Hδ₂,
    existsi δ,
    split,
    assumption,
    intros x' Hx',
    let HD := Hδ₂ x' Hx',
    rewrite [-abs_neg, neg_neg_sub_neg],
    exact HD
  end

theorem translate_continuous_of_continuous {f : ℝ → ℝ} (Hcon : continuous f) (a : ℝ) :
        continuous (λ x, (f x) + a) :=
  begin
    intros x ε Hε,
    cases Hcon x Hε with δ Hδ,
    cases Hδ with Hδ₁ Hδ₂,
    existsi δ,
    split,
    assumption,
    intros x' Hx',
    rewrite [add_sub_comm, sub_self, algebra.add_zero],
    apply Hδ₂,
    assumption
  end
end continuous

section inter_val
open set

private definition inter_sup (a b : ℝ) (f : ℝ → ℝ) := sup {x | x < b ∧ f x < 0}

section
parameters {f : ℝ → ℝ} (Hf : continuous f) {a b : ℝ} (Hab : a < b) (Ha : f a < 0) (Hb : f b > 0)
include Hf Ha Hb Hab

private theorem Hinh : ∃ x, x ∈ {x | x < b ∧ f x < 0} := exists.intro a (and.intro Hab Ha)

private theorem Hmem : ∀ x, x ∈ {x | x < b ∧ f x < 0} → x ≤ b := λ x Hx, le_of_lt (and.left Hx)

private theorem Hsupleb : inter_sup a b f ≤ b := sup_le (Hinh) Hmem

local notation 2 := of_num 1 + of_num 1

private theorem ex_delta_lt {x : ℝ} (Hx : f x < 0) (Hxb : x < b) : ∃ δ : ℝ, δ > 0 ∧ x + δ < b ∧ f (x + δ) < 0 :=
  begin
    let Hcont := neg_on_nbhd_of_cts_of_neg Hf Hx,
    cases Hcont with δ Hδ,
    {cases em (x + δ < b) with Haδ Haδ,
    existsi δ / 2,
    split,
    {exact div_pos_of_pos_of_pos (and.left Hδ) two_pos},
    split,
    {apply lt.trans,
    apply add_lt_add_left,
    exact div_two_lt_of_pos (and.left Hδ),
    exact Haδ},
    {apply and.right Hδ,
    krewrite [sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg,
             abs_of_pos (div_pos_of_pos_of_pos (and.left Hδ) two_pos)],
    exact div_two_lt_of_pos (and.left Hδ)},
    existsi (b - x) / 2,
    split,
    {apply div_pos_of_pos_of_pos,
    exact sub_pos_of_lt Hxb,
    exact two_pos},
    split,
    {apply add_midpoint Hxb},
    {apply and.right Hδ,
    krewrite [sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg,
            abs_of_pos (div_pos_of_pos_of_pos (sub_pos_of_lt Hxb) two_pos)],
    apply lt_of_lt_of_le,
    apply div_two_lt_of_pos (sub_pos_of_lt Hxb),
    apply sub_left_le_of_le_add,
    apply le_of_not_gt Haδ}}
  end

private lemma sup_near_b {δ : ℝ} (Hpos : 0 < δ)
                (Hgeb : inter_sup a b f + δ / 2 ≥ b) : abs (inter_sup a b f - b) < δ :=
  begin
    apply abs_lt_of_lt_of_neg_lt,
    apply sub_lt_left_of_lt_add,
    apply lt_of_le_of_lt,
    apply Hsupleb,
    apply lt_add_of_pos_right Hpos,
    rewrite neg_sub,
    apply sub_lt_left_of_lt_add,
    apply lt_of_le_of_lt,
    apply Hgeb,
    apply add_lt_add_left,
    apply div_two_lt_of_pos Hpos
  end

private lemma delta_of_lt (Hflt : f (inter_sup a b f) < 0) :
              ∃ δ : ℝ, δ > 0 ∧ inter_sup a b f + δ < b ∧ f (inter_sup a b f + δ) < 0 :=
  if Hlt : inter_sup a b f < b then ex_delta_lt Hflt Hlt else
  begin
    let Heq := eq_of_le_of_ge Hsupleb (le_of_not_gt Hlt),
    apply absurd Hflt,
    apply not_lt_of_ge,
    apply le_of_lt,
    rewrite Heq,
    exact Hb
  end

private theorem sup_fn_interval_aux1 : f (inter_sup a b f) ≥ 0 :=
  have ¬ f (inter_sup a b f) < 0, from
    (suppose  f (inter_sup a b f) < 0,
     obtain δ Hδ, from delta_of_lt this,
     have inter_sup a b f + δ ∈ {x | x < b ∧ f x < 0},
       from and.intro (and.left (and.right Hδ)) (and.right (and.right Hδ)),
     have ¬ inter_sup a b f < inter_sup a b f + δ,
       from not_lt_of_ge (le_sup this Hmem),
     show false, from this (lt_add_of_pos_right (and.left Hδ))),
  le_of_not_gt this

private theorem sup_fn_interval_aux2 : f (inter_sup a b f) ≤ 0 :=
  have ¬ f (inter_sup a b f) > 0, from
  (assume Hfsup : f (inter_sup a b f) > 0,
    obtain δ Hδ, from pos_on_nbhd_of_cts_of_pos Hf Hfsup,
    have ∀ x, x ∈ {x | x < b ∧ f x < 0} → x ≤ inter_sup a b f - δ / 2, from
     (take x, assume Hxset : x ∈ {x | x < b ∧ f x < 0},
      have ¬ x > inter_sup a b f - δ / 2, from
        (assume Hngt,
         have Habs : abs (inter_sup a b f - x) < δ, begin
           apply abs_lt_of_lt_of_neg_lt,
           apply sub_lt_of_sub_lt,
           apply gt.trans,
           exact Hngt,
           apply sub_lt_sub_left,
           exact div_two_lt_of_pos (and.left Hδ),
           rewrite neg_sub,
           apply lt_of_le_of_lt,
           rotate 1,
           apply and.left Hδ,
           apply sub_nonpos_of_le,
           apply le_sup,
           exact Hxset,
           exact Hmem
         end,
         have f x > 0, from and.right Hδ x Habs,
         show false, from (not_lt_of_gt this) (and.right Hxset)),
      le_of_not_gt this),
    have Hle : inter_sup a b f ≤ inter_sup a b f - δ / 2, from sup_le Hinh this,
    show false, from not_le_of_gt
                     (sub_lt_of_pos _ (div_pos_of_pos_of_pos (and.left Hδ) (two_pos))) Hle),
  le_of_not_gt this

private theorem sup_fn_interval : f (inter_sup a b f) = 0 :=
  eq_of_le_of_ge sup_fn_interval_aux2 sup_fn_interval_aux1


private theorem intermediate_value_incr_aux2 : ∃ δ : ℝ, δ > 0 ∧ a + δ < b ∧ f (a + δ) < 0 :=
  begin
    let Hcont := neg_on_nbhd_of_cts_of_neg Hf Ha,
    cases Hcont with δ Hδ,
    {cases em (a + δ < b) with Haδ Haδ,
    existsi δ / 2,
    split,
    {exact div_pos_of_pos_of_pos (and.left Hδ) two_pos},
    split,
    {apply lt.trans,
    apply add_lt_add_left,
    exact div_two_lt_of_pos (and.left Hδ),
    exact Haδ},
    {apply and.right Hδ,
    krewrite [sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg,
             abs_of_pos (div_pos_of_pos_of_pos (and.left Hδ) two_pos)],
    exact div_two_lt_of_pos (and.left Hδ)},
    existsi (b - a) / 2,
    split,
    {apply div_pos_of_pos_of_pos,
    exact sub_pos_of_lt Hab,
    exact two_pos},
    split,
    {apply add_midpoint Hab},
    {apply and.right Hδ,
    krewrite [sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg,
            abs_of_pos (div_pos_of_pos_of_pos (sub_pos_of_lt Hab) two_pos)],
    apply lt_of_lt_of_le,
    apply div_two_lt_of_pos (sub_pos_of_lt Hab),
    apply sub_left_le_of_le_add,
    apply le_of_not_gt Haδ}}
  end

theorem intermediate_value_incr_zero : ∃ c, a < c ∧ c < b ∧ f c = 0 :=
  begin
    existsi inter_sup a b f,
    split,
    {cases intermediate_value_incr_aux2 with δ Hδ,
    apply lt_of_lt_of_le,
    apply lt_add_of_pos_right,
    exact and.left Hδ,
    apply le_sup,
    exact and.right Hδ,
    intro x Hx,
    apply le_of_lt,
    exact and.left Hx},
    split,
    {cases pos_on_nbhd_of_cts_of_pos Hf Hb with δ Hδ,
    apply lt_of_le_of_lt,
    rotate 1,
    apply sub_lt_of_pos,
    exact and.left Hδ,
    rotate_right 1,
    apply sup_le,
    exact exists.intro a (and.intro Hab Ha),
    intro x Hx,
    apply le_of_not_gt,
    intro Hxgt,
    have Hxgt' : b - x < δ, from sub_lt_of_sub_lt Hxgt,
    krewrite -(abs_of_pos (sub_pos_of_lt (and.left Hx))) at Hxgt',
    let Hxgt'' := and.right Hδ _ Hxgt',
    exact not_lt_of_ge (le_of_lt Hxgt'') (and.right Hx)},
    {exact sup_fn_interval}
  end

end

theorem intermediate_value_decr_zero {f : ℝ → ℝ} (Hf : continuous f) {a b : ℝ} (Hab : a < b)
        (Ha : f a > 0) (Hb : f b < 0) : ∃ c, a < c ∧ c < b ∧ f c = 0 :=
  begin
    have Ha' : - f a < 0, from neg_neg_of_pos Ha,
    have Hb' : - f b > 0, from neg_pos_of_neg Hb,
    have Hcon : continuous (λ x, - f x), from neg_continuous_of_continuous Hf,
    let Hiv := intermediate_value_incr_zero Hcon Hab Ha' Hb',
    cases Hiv with c Hc,
    existsi c,
    split,
    exact and.left Hc,
    split,
    exact and.left (and.right Hc),
    apply eq_zero_of_neg_eq_zero,
    apply and.right (and.right Hc)
  end

theorem intermediate_value_incr {f : ℝ → ℝ} (Hf : continuous f) {a b : ℝ} (Hab : a < b) {v : ℝ}
        (Hav : f a < v) (Hbv : f b > v) : ∃ c, a < c ∧ c < b ∧ f c = v :=
  have Hav' : f a - v < 0, from sub_neg_of_lt Hav,
  have Hbv' : f b - v > 0, from sub_pos_of_lt Hbv,
  have Hcon : continuous (λ x, f x - v), from translate_continuous_of_continuous Hf _,
  have Hiv : ∃ c, a < c ∧ c < b ∧ f c - v = 0, from intermediate_value_incr_zero Hcon Hab Hav' Hbv',
  obtain c Hc, from Hiv,
  exists.intro c
    (and.intro (and.left Hc) (and.intro (and.left (and.right Hc)) (eq_of_sub_eq_zero (and.right (and.right Hc)))))

theorem intermediate_value_decr {f : ℝ → ℝ} (Hf : continuous f) {a b : ℝ} (Hab : a < b) {v : ℝ}
        (Hav : f a > v) (Hbv : f b < v) : ∃ c, a < c ∧ c < b ∧ f c = v :=
  have Hav' : f a - v > 0, from sub_pos_of_lt Hav,
  have Hbv' : f b - v < 0, from sub_neg_of_lt Hbv,
  have Hcon : continuous (λ x, f x - v), from translate_continuous_of_continuous Hf _,
  have Hiv : ∃ c, a < c ∧ c < b ∧ f c - v = 0, from intermediate_value_decr_zero Hcon Hab Hav' Hbv',
  obtain c Hc, from Hiv,
  exists.intro c
    (and.intro (and.left Hc) (and.intro (and.left (and.right Hc)) (eq_of_sub_eq_zero (and.right (and.right Hc)))))

end inter_val

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

end real
