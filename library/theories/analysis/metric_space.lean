/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Metric spaces.
-/
import data.real.complete data.pnat data.list.sort
open nat real eq.ops classical

structure metric_space [class] (M : Type) : Type :=
  (dist : M → M → ℝ)
  (dist_self : ∀ x : M, dist x x = 0)
  (eq_of_dist_eq_zero : ∀ {x y : M}, dist x y = 0 → x = y)
  (dist_comm : ∀ x y : M, dist x y = dist y x)
  (dist_triangle : ∀ x y z : M, dist x z ≤ dist x y + dist y z)

namespace analysis

section metric_space_M
variables {M : Type} [metric_space M]

definition dist (x y : M) : ℝ := metric_space.dist x y

proposition dist_self (x : M) : dist x x = 0 := metric_space.dist_self x

proposition eq_of_dist_eq_zero {x y : M} (H : dist x y = 0) : x = y :=
metric_space.eq_of_dist_eq_zero H

proposition dist_comm (x y : M) : dist x y = dist y x := metric_space.dist_comm x y

proposition dist_eq_zero_iff (x y : M) : dist x y = 0 ↔ x = y :=
iff.intro eq_of_dist_eq_zero (suppose x = y, this ▸ !dist_self)

proposition dist_triangle (x y z : M) : dist x z ≤ dist x y + dist y z :=
metric_space.dist_triangle x y z

proposition dist_nonneg (x y : M) : 0 ≤ dist x y :=
have dist x y + dist y x ≥ 0, by rewrite -(dist_self x); apply dist_triangle,
have 2 * dist x y ≥ 0, using this,
  by krewrite [-real.one_add_one, right_distrib, +one_mul, dist_comm at {2}]; apply this,
nonneg_of_mul_nonneg_left this two_pos

proposition dist_pos_of_ne {x y : M} (H : x ≠ y) : dist x y > 0 :=
lt_of_le_of_ne !dist_nonneg (suppose 0 = dist x y, H (iff.mp !dist_eq_zero_iff this⁻¹))

proposition ne_of_dist_pos {x y : M} (H : dist x y > 0) : x ≠ y :=
suppose x = y,
have H1 [visible] : dist x x > 0, by rewrite this at {2}; exact H,
by rewrite dist_self at H1; apply not_lt_self _ H1

proposition eq_of_forall_dist_le {x y : M} (H : ∀ ε, ε > 0 → dist x y ≤ ε) : x = y :=
eq_of_dist_eq_zero (eq_zero_of_nonneg_of_forall_le !dist_nonneg H)

/- convergence of a sequence -/

definition converges_to_seq (X : ℕ → M) (y : M) : Prop :=
∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ ⦃n⦄, n ≥ N → dist (X n) y < ε

-- the same, with ≤ in place of <; easier to prove, harder to use
definition converges_to_seq.intro {X : ℕ → M} {y : M}
    (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → dist (X n) y ≤ ε) :
  converges_to_seq X y :=
take ε, assume epos : ε > 0,
  have e2pos : ε / 2 > 0, from  div_pos_of_pos_of_pos `ε > 0` two_pos,
  obtain N HN, from H e2pos,
  exists.intro N
    (take n, suppose n ≥ N,
      calc
        dist (X n) y ≤ ε / 2 : HN _ `n ≥ N`
                 ... < ε     : div_two_lt_of_pos epos)

notation X `⟶` y `in` `ℕ` := converges_to_seq X y

definition converges_seq [class] (X : ℕ → M) : Prop := ∃ y, X ⟶ y in ℕ

noncomputable definition limit_seq (X : ℕ → M) [H : converges_seq X] : M := some H

proposition converges_to_limit_seq (X : ℕ → M) [H : converges_seq X] :
  (X ⟶ limit_seq X in ℕ) :=
some_spec H

proposition converges_to_seq_unique {X : ℕ → M} {y₁ y₂ : M}
  (H₁ : X ⟶ y₁ in ℕ) (H₂ : X ⟶ y₂ in ℕ) : y₁ = y₂ :=
eq_of_forall_dist_le
  (take ε, suppose ε > 0,
    have e2pos : ε / 2 > 0, from  div_pos_of_pos_of_pos `ε > 0` two_pos,
    obtain N₁ (HN₁ : ∀ {n}, n ≥ N₁ → dist (X n) y₁ < ε / 2), from H₁ e2pos,
    obtain N₂ (HN₂ : ∀ {n}, n ≥ N₂ → dist (X n) y₂ < ε / 2), from H₂ e2pos,
    let N := max N₁ N₂ in
    have dN₁ : dist (X N) y₁ < ε / 2, from HN₁ !le_max_left,
    have dN₂ : dist (X N) y₂ < ε / 2, from HN₂ !le_max_right,
    have dist y₁ y₂ < ε, from calc
      dist y₁ y₂ ≤ dist y₁ (X N) + dist (X N) y₂ : dist_triangle
             ... = dist (X N) y₁ + dist (X N) y₂ : dist_comm
             ... < ε / 2 + ε / 2                 : add_lt_add dN₁ dN₂
             ... = ε                             : add_halves,
    show dist y₁ y₂ ≤ ε, from le_of_lt this)

proposition eq_limit_of_converges_to_seq {X : ℕ → M} {y : M} (H : X ⟶ y in ℕ) :
  y = @limit_seq M _ X (exists.intro y H) :=
converges_to_seq_unique H (@converges_to_limit_seq M _ X (exists.intro y H))

proposition converges_to_seq_constant (y : M) : (λn, y) ⟶ y in ℕ :=
take ε, assume egt0 : ε > 0,
exists.intro 0
  (take n, suppose n ≥ 0,
    calc
      dist y y = 0 : !dist_self
           ... < ε : egt0)

proposition converges_to_seq_offset {X : ℕ → M} {y : M} (k : ℕ) (H : X ⟶ y in ℕ) :
  (λ n, X (n + k)) ⟶ y in ℕ :=
take ε, suppose ε > 0,
obtain N HN, from H `ε > 0`,
exists.intro N
  (take n : ℕ, assume ngtN : n ≥ N,
    show dist (X (n + k)) y < ε, from HN (n + k) (le.trans ngtN !le_add_right))

proposition converges_to_seq_offset_left {X : ℕ → M} {y : M} (k : ℕ) (H : X ⟶ y in ℕ) :
  (λ n, X (k + n)) ⟶ y in ℕ :=
have aux : (λ n, X (k + n)) = (λ n, X (n + k)), from funext (take n, by rewrite add.comm),
by+ rewrite aux; exact converges_to_seq_offset k H

proposition converges_to_seq_offset_succ {X : ℕ → M} {y : M} (H : X ⟶ y in ℕ) :
  (λ n, X (succ n)) ⟶ y in ℕ :=
converges_to_seq_offset 1 H

proposition converges_to_seq_of_converges_to_seq_offset
    {X : ℕ → M} {y : M} {k : ℕ} (H : (λ n, X (n + k)) ⟶ y in ℕ) :
  X ⟶ y in ℕ :=
take ε, suppose ε > 0,
obtain N HN, from H `ε > 0`,
exists.intro (N + k)
  (take n : ℕ, assume nge : n ≥ N + k,
    have n - k ≥ N, from nat.le_sub_of_add_le nge,
    have dist (X (n - k + k)) y < ε, from HN (n - k) this,
    show dist (X n) y < ε, using this,
      by rewrite [(nat.sub_add_cancel (le.trans !le_add_left nge)) at this]; exact this)

proposition converges_to_seq_of_converges_to_seq_offset_left
    {X : ℕ → M} {y : M} {k : ℕ} (H : (λ n, X (k + n)) ⟶ y in ℕ) :
  X ⟶ y in ℕ :=
have aux : (λ n, X (k + n)) = (λ n, X (n + k)), from funext (take n, by rewrite add.comm),
by+ rewrite aux at H; exact converges_to_seq_of_converges_to_seq_offset H

proposition converges_to_seq_of_converges_to_seq_offset_succ
    {X : ℕ → M} {y : M} (H : (λ n, X (succ n)) ⟶ y in ℕ) :
  X ⟶ y in ℕ :=
@converges_to_seq_of_converges_to_seq_offset M _ X y 1 H

proposition converges_to_seq_offset_iff (X : ℕ → M) (y : M) (k : ℕ) :
  ((λ n, X (n + k)) ⟶ y in ℕ) ↔ (X ⟶ y in ℕ) :=
iff.intro converges_to_seq_of_converges_to_seq_offset !converges_to_seq_offset

proposition converges_to_seq_offset_left_iff (X : ℕ → M) (y : M) (k : ℕ) :
  ((λ n, X (k + n)) ⟶ y in ℕ) ↔ (X ⟶ y in ℕ) :=
iff.intro converges_to_seq_of_converges_to_seq_offset_left !converges_to_seq_offset_left

proposition converges_to_seq_offset_succ_iff (X : ℕ → M) (y : M) :
  ((λ n, X (succ n)) ⟶ y in ℕ) ↔ (X ⟶ y in ℕ) :=
iff.intro converges_to_seq_of_converges_to_seq_offset_succ !converges_to_seq_offset_succ

section
open list
definition r_trans : transitive (@le ℝ _) := λ a b c, !le.trans
definition r_refl : reflexive (@le ℝ _) := λ a, !le.refl

theorem dec_prf_eq (P : Prop) (H1 H2 : decidable P) : H1 = H2 :=
  begin
    induction H1,
    induction H2,
    reflexivity,
    apply absurd a a_1,
    induction H2,
    apply absurd a_1 a,
    reflexivity
  end

-- there's a very ugly part of this proof.

proposition bounded_of_converges_seq {X : ℕ → M} {x : M} (H : X ⟶ x in ℕ) :
            ∃ K : ℝ, ∀ n : ℕ, dist (X n) x ≤ K :=
  begin
    cases H zero_lt_one with N HN,
    cases em (N = 0),
    existsi 1,
    intro n,
    apply le_of_lt,
    apply HN,
    rewrite a,
    apply zero_le,
    let l := map (λ n : ℕ, -dist (X n) x) (upto N),
    have Hnenil : l ≠ nil, from (map_ne_nil_of_ne_nil _ (upto_ne_nil_of_ne_zero a)),
    existsi max (-list.min (λ a b : ℝ, le a b) l Hnenil) 1,
    intro n,
    have Hsmn : ∀ m : ℕ, m < N → dist (X m) x ≤ max (-list.min (λ a b : ℝ, le a b) l Hnenil) 1, begin
      intro m Hm,
      apply le.trans,
      rotate 1,
      apply le_max_left,
      note Hall := min_lemma real.le_total r_trans r_refl Hnenil,
      have Hmem : -dist (X m) x ∈ (map (λ (n : ℕ), -dist (X n) x) (upto N)), from mem_map _ (mem_upto_of_lt Hm),
      note Hallm' := of_mem_of_all Hmem Hall,
      apply le_neg_of_le_neg,
      esimp, esimp at Hallm',
      have Heqs : (λ (a b : real), classical.prop_decidable (@le.{1} real real.real_has_le a b))
                   =
                   (@decidable_le.{1} real
                     (@decidable_linear_ordered_comm_group.to_decidable_linear_order.{1} real
                        (@decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_comm_group.{1} real
                           (@discrete_linear_ordered_field.to_decidable_linear_ordered_comm_ring.{1} real
                             real.discrete_linear_ordered_field)))),
      begin
        apply funext, intro, apply funext, intro,
        apply dec_prf_eq
      end,
      rewrite -Heqs,
      exact Hallm'
    end,
    cases em (n < N) with Elt Ege,
    apply Hsmn,
    exact Elt,
    apply le_of_lt,
    apply lt_of_lt_of_le,
    apply HN,
    apply le_of_not_gt Ege,
    apply le_max_right
  end
end

/- cauchy sequences -/

definition cauchy (X : ℕ → M) : Prop :=
∀ ε : ℝ, ε > 0 → ∃ N, ∀ m n, m ≥ N → n ≥ N → dist (X m) (X n) < ε

proposition cauchy_of_converges_seq (X : ℕ → M) [H : converges_seq X] : cauchy X :=
take ε, suppose ε > 0,
  obtain y (Hy : converges_to_seq X y), from H,
  have e2pos : ε / 2 > 0, from div_pos_of_pos_of_pos `ε > 0` two_pos,
  obtain N₁ (HN₁ : ∀ {n}, n ≥ N₁ → dist (X n) y < ε / 2), from Hy e2pos,
  obtain N₂ (HN₂ : ∀ {n}, n ≥ N₂ → dist (X n) y < ε / 2), from Hy e2pos,
  let N := max N₁ N₂ in
    exists.intro N
      (take m n, suppose m ≥ N, suppose n ≥ N,
        have m ≥ N₁, from le.trans !le_max_left `m ≥ N`,
        have n ≥ N₂, from le.trans !le_max_right `n ≥ N`,
        have dN₁ : dist (X m) y < ε / 2, from HN₁ `m ≥ N₁`,
        have dN₂ : dist (X n) y < ε / 2, from HN₂ `n ≥ N₂`,
        show dist (X m) (X n) < ε, from calc
          dist (X m) (X n) ≤ dist (X m) y + dist y (X n) : dist_triangle
                       ... = dist (X m) y + dist (X n) y : dist_comm
                       ... < ε / 2 + ε / 2               : add_lt_add dN₁ dN₂
                       ... = ε                           : add_halves)

end metric_space_M

/- convergence of a function at a point -/

section metric_space_M_N
variables {M N : Type} [strucM : metric_space M] [strucN : metric_space N]
include strucM strucN

definition converges_to_at (f : M → N) (y : N) (x : M) :=
∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, x' ≠ x ∧ dist x' x < δ → dist (f x') y < ε

notation f `⟶` y `at` x := converges_to_at f y x

definition converges_at [class] (f : M → N) (x : M) :=
∃ y, converges_to_at f y x

noncomputable definition limit_at (f : M → N) (x : M) [H : converges_at f x] : N :=
some H

proposition converges_to_limit_at (f : M → N) (x : M) [H : converges_at f x] :
  (f ⟶ limit_at f x at x) :=
some_spec H

/- continuity at a point -/

definition continuous_at (f : M → N) (x : M) :=
∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → dist (f x') (f x) < ε

theorem continuous_at_of_converges_to_at {f : M → N} {x : M} (Hf : f ⟶ f x at x) :
  continuous_at f x :=
take ε, suppose ε > 0,
obtain δ Hδ, from Hf this,
exists.intro δ (and.intro
  (and.left Hδ)
  (take x', suppose dist x' x < δ,
   if Heq : x' = x then
     by rewrite [-Heq, dist_self]; assumption
   else
     (suffices dist x' x < δ, from and.right Hδ x' (and.intro Heq this),
      this)))

theorem converges_to_at_of_continuous_at {f : M → N} {x : M} (Hf : continuous_at f x) :
  f ⟶ f x at x :=
take ε, suppose ε > 0,
obtain δ Hδ, from Hf this,
exists.intro δ (and.intro
  (and.left Hδ)
  (take x',
    assume H : x' ≠ x ∧ dist x' x < δ,
    show dist (f x') (f x) < ε, from and.right Hδ x' (and.right H)))

section
omit strucN
set_option pp.coercions true
--set_option pp.all true

open pnat rat

section
omit strucM

private lemma of_rat_rat_of_pnat_eq_of_nat_nat_of_pnat (p : pnat) :
        of_rat (rat_of_pnat p) = of_nat (nat_of_pnat p) :=
  rfl

end

theorem cnv_real_of_cnv_nat {X : ℕ → M} {c : M} (H : ∀ n : ℕ, dist (X n) c < 1 / (real.of_nat n + 1)) :
        ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → dist (X n) c < ε :=
  begin
    intros ε Hε,
    cases ex_rat_pos_lower_bound_of_pos Hε with q Hq,
    cases Hq with Hq1 Hq2,
    cases pnat_bound Hq1 with p Hp,
    existsi nat_of_pnat p,
    intros n Hn,
    apply lt_of_lt_of_le,
    apply H,
    apply le.trans,
    rotate 1,
    apply Hq2,
    have Hrat : of_rat (inv p) ≤ of_rat q, from of_rat_le_of_rat_of_le Hp,
    apply le.trans,
    rotate 1,
    exact Hrat,
    change 1 / (of_nat n + 1) ≤ of_rat ((1 : ℚ) / (rat_of_pnat p)),
    rewrite [of_rat_divide, of_rat_one],
    eapply one_div_le_one_div_of_le,
    krewrite -of_rat_zero,
    apply of_rat_lt_of_rat_of_lt,
    apply rat_of_pnat_is_pos,
    krewrite [of_rat_rat_of_pnat_eq_of_nat_nat_of_pnat, -real.of_nat_add],
    apply real.of_nat_le_of_nat_of_le,
    apply le_add_of_le_right,
    assumption
  end
end

theorem all_conv_seqs_of_converges_to_at {f : M → N} {c : M} {l : N} (Hconv : f ⟶ l at c) :
        ∀ X : ℕ → M, ((∀ n : ℕ, ((X n) ≠ c) ∧ (X ⟶ c in ℕ)) → ((λ n : ℕ, f (X n)) ⟶ l in ℕ)) :=
   begin
     intros X HX,
     rewrite [↑converges_to_at at Hconv, ↑converges_to_seq],
     intros ε Hε,
     cases Hconv Hε with δ Hδ,
     cases Hδ with Hδ1 Hδ2,
     cases HX 0 with _ HXlim,
     cases HXlim Hδ1 with N1 HN1,
     existsi N1,
     intro n Hn,
     apply Hδ2,
     split,
     apply and.left (HX _),
     exact HN1 Hn
   end

theorem converges_to_at_of_all_conv_seqs {f : M → N} (c : M) (l : N)
  (Hseq : ∀ X : ℕ → M, ((∀ n : ℕ, ((X n) ≠ c) ∧ (X ⟶ c in ℕ)) → ((λ n : ℕ, f (X n)) ⟶ l in ℕ)))
  : f ⟶ l at c :=
  by_contradiction
    (assume Hnot : ¬ (f ⟶ l at c),
    obtain ε Hε, from exists_not_of_not_forall Hnot,
    let Hε' := iff.mp not_implies_iff_and_not Hε in
    obtain (H1 : ε > 0) H2, from Hε',
    have H3 [visible] : ∀ δ : ℝ, (δ > 0 → ∃ x' : M, x' ≠ c ∧ dist x' c < δ ∧ dist (f x') l ≥ ε), begin -- tedious!!
      intros δ Hδ,
      note Hε'' := forall_not_of_not_exists H2,
      note H4 := forall_not_of_not_exists H2 δ,
      have ¬ (∀ x' : M, x' ≠ c ∧ dist x' c < δ → dist (f x') l < ε), from λ H', H4 (and.intro Hδ H'),
      note H5 := exists_not_of_not_forall this,
      cases H5 with x' Hx',
      existsi x',
      note H6 := iff.mp not_implies_iff_and_not Hx',
      rewrite and.assoc at H6,
      cases H6,
      split,
      assumption,
      cases a_1,
      split,
      assumption,
      apply le_of_not_gt,
      assumption
    end,
    let S : ℕ → M → Prop := λ n x, 0 < dist x c ∧ dist x c < 1 / (of_nat n + 1) ∧ dist (f x) l ≥ ε in
    have HS [visible] : ∀ n : ℕ, ∃ m : M, S n m, begin
      intro k,
      have Hpos : 0 < of_nat k + 1, from of_nat_succ_pos k,
      cases H3 (1 / (k + 1)) (one_div_pos_of_pos Hpos) with x' Hx',
      cases Hx' with Hne Hx',
      cases Hx' with Hdistl Hdistg,
      existsi x',
      esimp,
      split,
      apply dist_pos_of_ne,
      assumption,
      split,
      repeat assumption
    end,
    let X : ℕ → M := λ n, some (HS n) in
    have H4 [visible] : ∀ n : ℕ, ((X n) ≠ c) ∧ (X ⟶ c in ℕ), from
      (take n, and.intro
        (begin
          note Hspec := some_spec (HS n),
          esimp, esimp at Hspec,
          cases Hspec,
          apply ne_of_dist_pos,
          assumption
        end)
        (begin
          apply cnv_real_of_cnv_nat,
          intro m,
          note Hspec := some_spec (HS m),
          esimp, esimp at Hspec,
          cases Hspec with Hspec1 Hspec2,
          cases Hspec2,
          assumption
        end)),
    have H5 [visible] : (λ n : ℕ, f (X n)) ⟶ l in ℕ, from Hseq X H4,
    begin
      note H6 := H5 H1,
      cases H6 with Q HQ,
      note HQ' := HQ !le.refl,
      esimp at HQ',
      apply absurd HQ',
      apply not_lt_of_ge,
      note H7 := some_spec (HS Q),
      esimp at H7,
      cases H7 with H71 H72,
      cases H72,
      assumption
    end)

definition continuous (f : M → N) : Prop := ∀ x, continuous_at f x

theorem converges_seq_comp_of_converges_seq_of_cts [instance] (X : ℕ → M) [HX : converges_seq X] {f : M → N}
                                         (Hf : continuous f) :
        converges_seq (λ n, f (X n)) :=
  begin
    cases HX with xlim Hxlim,
    existsi f xlim,
    rewrite ↑converges_to_seq at *,
    intros ε Hε,
    let Hcont := Hf xlim Hε,
    cases Hcont with δ Hδ,
    cases Hxlim (and.left Hδ) with B HB,
    existsi B,
    intro n Hn,
    apply and.right Hδ,
    apply HB Hn
  end

omit strucN

theorem id_continuous : continuous (λ x : M, x) :=
  begin
    intros x ε Hε,
    existsi ε,
    split,
    assumption,
    intros,
    assumption
  end

end metric_space_M_N

end analysis

/- complete metric spaces -/

structure complete_metric_space [class] (M : Type) extends metricM : metric_space M : Type :=
(complete : ∀ X, @analysis.cauchy M metricM X → @analysis.converges_seq M metricM X)

namespace analysis

proposition complete (M : Type) [cmM : complete_metric_space M] {X : ℕ → M} (H : cauchy X) :
  converges_seq X :=
complete_metric_space.complete X H

end analysis

/- the reals form a metric space -/

noncomputable definition metric_space_real [instance] : metric_space ℝ :=
⦃ metric_space,
  dist               := λ x y, abs (x - y),
  dist_self          := λ x, abstract by rewrite [sub_self, abs_zero] end,
  eq_of_dist_eq_zero := λ x y, eq_of_abs_sub_eq_zero,
  dist_comm          := abs_sub,
  dist_triangle      := abs_sub_le
⦄
