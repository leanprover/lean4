/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

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
open real eq.ops classical
noncomputable theory

namespace real

/- the reals form a metric space -/

protected definition to_metric_space [instance] : metric_space ℝ :=
⦃ metric_space,
  dist               := λ x y, abs (x - y),
  dist_self          := λ x, abstract by rewrite [sub_self, abs_zero] end,
  eq_of_dist_eq_zero := @eq_of_abs_sub_eq_zero,
  dist_comm          := abs_sub,
  dist_triangle      := abs_sub_le
⦄

open nat

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
  have H1 : (rat.gt k⁻¹ (rat.of_num 0)), from !inv_pos,
  have H2 : (of_rat k⁻¹ > of_rat (rat.of_num 0)), from !of_rat_lt_of_rat_of_lt H1,
  obtain (N : ℕ) (H : ∀ m n, m ≥ N → n ≥ N → abs (X m - X n) < of_rat k⁻¹), from H _ H2,
  exists.intro (pnat.succ N)
    (take m n : ℕ+,
      assume Hm : m ≥ (pnat.succ N),
      assume Hn : n ≥ (pnat.succ N),
      have Hm' : elt_of m ≥ N, from nat.le.trans !le_succ Hm,
      have Hn' : elt_of n ≥ N, from nat.le.trans !le_succ Hn,
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
        have abs (X n - l) ≤ real.of_rat k⁻¹, from conv k n' Hn,
        show abs (X n - l) < ε, from lt_of_le_of_lt this Hk))

/- sup and inf -/

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

end

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
