/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Metric spaces.
-/
import data.real.complete data.pnat data.list.sort ..topology.basic data.set
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


end metric_space_M_N

section topology
/- A metric space is a topological space. -/

open set prod topology

variables {V : Type} [Vmet : metric_space V]
include Vmet

definition open_ball (x : V) (ε : ℝ) := {y ∈ univ | dist x y < ε}

theorem open_ball_empty_of_nonpos (x : V) {ε : ℝ} (Hε : ε ≤ 0) : open_ball x ε = ∅ :=
  begin
    apply eq_empty_of_forall_not_mem,
    intro y Hy,
    note Hlt := and.right Hy,
    apply not_lt_of_ge (dist_nonneg x y),
    apply lt_of_lt_of_le Hlt Hε
  end

theorem radius_pos_of_nonempty {x : V} {ε : ℝ} {u : V} (Hu : u ∈ open_ball x ε) : ε > 0 :=
  begin
    apply lt_of_not_ge,
    intro Hge,
    note Hop := open_ball_empty_of_nonpos x Hge,
    rewrite Hop at Hu,
    apply not_mem_empty _ Hu
  end

theorem mem_open_ball (x : V) {ε : ℝ} (H : ε > 0) : x ∈ open_ball x ε :=
  suffices x ∈ univ ∧ dist x x < ε, from this,
  and.intro !mem_univ (by rewrite dist_self; assumption)

definition closed_ball (x : V) (ε : ℝ) := {y ∈ univ | dist x y ≤ ε}

theorem closed_ball_eq_comp (x : V) (ε : ℝ) : closed_ball x ε = -{y ∈ univ | dist x y > ε} :=
  begin
    apply ext,
    intro y,
    apply iff.intro,
    intro Hx,
    apply mem_comp,
    intro Hxmem,
    cases Hxmem with _ Hgt,
    cases Hx with _ Hle,
    apply not_le_of_gt Hgt Hle,
    intro Hx,
    note Hx' := not_mem_of_mem_comp Hx,
    split,
    apply mem_univ,
    apply le_of_not_gt,
    intro Hgt,
    apply Hx',
    split,
    apply mem_univ,
    assumption
  end

omit Vmet

definition open_sets_basis (V : Type) [metric_space V] :=
  image (λ pair : V × ℝ, open_ball (pr1 pair) (pr2 pair)) univ

definition metric_topology [instance] (V : Type) [metric_space V] : topology V :=
  topology.generated_by (open_sets_basis V)

include Vmet

theorem open_ball_mem_open_sets_basis (x : V) (ε : ℝ) : (open_ball x ε) ∈ (open_sets_basis V) :=
  mem_image !mem_univ rfl

theorem open_ball_open (x : V) (ε : ℝ) : Open (open_ball x ε) :=
  by apply generators_mem_topology_generated_by; apply open_ball_mem_open_sets_basis

theorem closed_ball_closed (x : V) {ε : ℝ} (H : ε > 0) : closed (closed_ball x ε) :=
  begin
    apply iff.mpr !closed_iff_Open_comp,
    rewrite closed_ball_eq_comp,
    rewrite comp_comp,
    apply Open_of_forall_exists_Open_nbhd,
    intro y Hy,
    cases Hy with _ Hxy,
    existsi open_ball y (dist x y - ε),
    split,
    apply open_ball_open,
    split,
    apply mem_open_ball,
    apply sub_pos_of_lt Hxy,
    intros y' Hy',
    cases Hy' with _ Hxy'd,
    rewrite dist_comm at Hxy'd,
    split,
    apply mem_univ,
    apply lt_of_not_ge,
    intro Hxy',
    apply not_lt_self (dist x y),
    exact calc
      dist x y ≤ dist x y' + dist y' y : dist_triangle
           ... ≤ ε         + dist y' y : add_le_add_right Hxy'
           ... < ε    + (dist x y - ε) : add_lt_add_left Hxy'd
           ... = dist x y              : by rewrite [add.comm, sub_add_cancel]
  end

theorem not_open_of_ex_boundary_pt {U : set V} {x : V} (HxU : x ∈ U)
        (Hbd : ∀ ε : ℝ, ε > 0 → ∃ v : V, v ∉ U ∧ dist x v < ε) : ¬ Open U :=
  begin
    intro HUopen,
    induction HUopen,
    {cases a with pr Hpr,
    cases pr with y r,
    cases Hpr with _ Hs,
    rewrite -Hs at HxU,
    have H : dist y x < r, from and.right HxU,
    cases Hbd _ (sub_pos_of_lt H) with v Hv,
    cases Hv with Hv Hvdist,
    apply Hv,
    rewrite -Hs,
    apply and.intro,
    apply mem_univ,
    apply lt_of_le_of_lt,
    apply dist_triangle,
    exact x,
    esimp,
    exact calc
      dist y x + dist x v < dist y x + (r - dist y x) : add_lt_add_left Hvdist
                      ... = r                         : by rewrite [add.comm, sub_add_cancel]},
    {cases Hbd 1 zero_lt_one with v Hv,
    cases Hv with Hv _,
    exact Hv !mem_univ},
    {have Hxs : x ∈ s, from mem_of_mem_inter_left HxU,
    have Hxt : x ∈ t, from mem_of_mem_inter_right HxU,
    note Hsih := exists_not_of_not_forall (v_0 Hxs),
    note Htih := exists_not_of_not_forall (v_1 Hxt),
    cases Hsih with ε1 Hε1,
    cases Htih with ε2 Hε2,
    note Hε1' := iff.mp not_implies_iff_and_not Hε1,
    note Hε2' := iff.mp not_implies_iff_and_not Hε2,
    cases Hε1' with Hε1p Hε1',
    cases Hε2' with Hε2p Hε2',
    note Hε1'' := forall_not_of_not_exists Hε1',
    note Hε2'' := forall_not_of_not_exists Hε2',
    have Hmin : min ε1 ε2 > 0, from lt_min Hε1p Hε2p,
    cases Hbd _ Hmin with v Hv,
    cases Hv with Hvint Hvdist,
    note Hε1v := Hε1'' v,
    note Hε2v := Hε2'' v,
    cases em (v ∉ s) with Hnm Hmem,
    apply Hε1v,
    split,
    exact Hnm,
    apply lt_of_lt_of_le Hvdist,
    apply min_le_left,
    apply Hε2v,
    have Hmem' : v ∈ s, from not_not_elim Hmem,
    note Hnm := not_mem_of_mem_of_not_mem_inter_left Hmem' Hvint,
    split,
    exact Hnm,
    apply lt_of_lt_of_le Hvdist,
    apply min_le_right},
    {have Hex : ∃₀ s ∈ S, x ∈ s, from HxU,
    cases Hex with s Hs,
    cases Hs with Hs Hxs,
    cases exists_not_of_not_forall (v_0 Hs Hxs) with ε Hε,
    cases iff.mp not_implies_iff_and_not Hε with Hεp Hv,
    cases Hbd _ Hεp with v Hv',
    cases Hv' with Hvnm Hdist,
    apply Hv,
    existsi v,
    split,
    apply not_mem_of_not_mem_sUnion Hvnm Hs,
    exact Hdist}
  end

theorem ex_Open_ball_subset_of_Open_of_nonempty {U : set V} (HU : Open U) {x : V} (Hx : x ∈ U) :
        ∃ (r : ℝ), r > 0 ∧ open_ball x r ⊆ U :=
  begin
    let balloon := {r ∈ univ | r > 0 ∧ open_ball x r ⊆ U},
    cases em (balloon = ∅),
    have H : ∀ r : ℝ, r > 0 → ∃ v : V, v ∉ U ∧ dist x v < r, begin
      intro r Hr,
      note Hor := iff.mp not_and_iff_not_or_not (forall_not_of_sep_empty a (mem_univ r)),
      note Hor' := or.neg_resolve_left Hor Hr,
      apply exists_of_not_forall_not,
      intro Hall,
      apply Hor',
      intro y Hy,
      cases iff.mp not_and_iff_not_or_not (Hall y) with Hmem Hge,
      apply not_not_elim Hmem,
      apply absurd (and.right Hy) Hge
    end,
    apply absurd HU,
    apply not_open_of_ex_boundary_pt Hx H,
    cases exists_mem_of_ne_empty a with r Hr,
    cases Hr with _ Hr,
    cases Hr with Hrpos HxrU,
    existsi r,
    split,
    repeat assumption
  end

end topology

section continuity
variables {M N : Type} [Hm : metric_space M] [Hn : metric_space N]
include Hm Hn
open topology set
/- continuity at a point -/

--definition continuous_at (f : M → N) (x : M) :=
--topology.continuous_at f x

-- the ε - δ definition of continuity is equivalent to the topological definition
theorem continuous_at_intro {f : M → N} {x : M}
        (H : ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → dist (f x') (f x) < ε) :
        continuous_at f x :=
  begin
    rewrite ↑continuous_at,
    intros U HfU Uopen,
    cases ex_Open_ball_subset_of_Open_of_nonempty Uopen HfU with r Hr,
    cases Hr with Hr HUr,
    cases H Hr with δ Hδ,
    cases Hδ with Hδ Hx'δ,
    existsi open_ball x δ,
    split,
    apply mem_open_ball,
    exact Hδ,
    split,
    apply open_ball_open,
    intro y Hy,
    apply HUr,
    cases Hy with y' Hy',
    cases Hy' with Hy' Hfy',
    cases Hy' with _ Hy',
    rewrite dist_comm at Hy',
    note Hy'' := Hx'δ Hy',
    apply and.intro !mem_univ,
    rewrite [-Hfy', dist_comm],
    exact Hy''
  end

theorem continuous_at_elim {f : M → N} {x : M} (Hfx : continuous_at f x) :
        ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ ⦃x'⦄, dist x' x < δ → dist (f x') (f x) < ε :=
  begin
    intros ε Hε,
    rewrite [↑continuous_at at Hfx],
    cases Hfx (open_ball (f x) ε) (mem_open_ball _ Hε) !open_ball_open with V HV,
    cases HV with HVx HV,
    cases HV with HV HVf,
    cases ex_Open_ball_subset_of_Open_of_nonempty HV HVx with δ Hδ,
    cases Hδ with Hδ Hδx,
    existsi δ,
    split,
    exact Hδ,
    intro x' Hx',
    rewrite dist_comm,
    apply and.right,
    apply HVf,
    existsi x',
    split,
    apply Hδx,
    apply and.intro !mem_univ,
    rewrite dist_comm,
    apply Hx',
    apply rfl
  end

theorem continuous_at_of_converges_to_at {f : M → N} {x : M} (Hf : f ⟶ f x at x) :
  continuous_at f x :=
continuous_at_intro
(take ε, suppose ε > 0,
obtain δ Hδ, from Hf this,
exists.intro δ (and.intro
  (and.left Hδ)
  (take x', suppose dist x' x < δ,
   if Heq : x' = x then
     by rewrite [-Heq, dist_self]; assumption
   else
     (suffices dist x' x < δ, from and.right Hδ x' (and.intro Heq this),
      this))))

theorem converges_to_at_of_continuous_at {f : M → N} {x : M} (Hf : continuous_at f x) :
  f ⟶ f x at x :=
take ε, suppose ε > 0,
obtain δ Hδ, from continuous_at_elim Hf this,
exists.intro δ (and.intro
  (and.left Hδ)
  (take x',
    assume H : x' ≠ x ∧ dist x' x < δ,
    show dist (f x') (f x) < ε, from and.right Hδ x' (and.right H)))


definition continuous (f : M → N) : Prop := ∀ x, continuous_at f x

theorem converges_seq_comp_of_converges_seq_of_cts [instance] (X : ℕ → M) [HX : converges_seq X] {f : M → N}
                                         (Hf : continuous f) :
        converges_seq (λ n, f (X n)) :=
  begin
    cases HX with xlim Hxlim,
    existsi f xlim,
    rewrite ↑converges_to_seq at *,
    intros ε Hε,
    let Hcont := (continuous_at_elim (Hf xlim)) Hε,
    cases Hcont with δ Hδ,
    cases Hxlim (and.left Hδ) with B HB,
    existsi B,
    intro n Hn,
    apply and.right Hδ,
    apply HB Hn
  end

omit Hn
theorem id_continuous : continuous (λ x : M, x) :=
  begin
    intros x,
    apply continuous_at_intro,
    intro ε Hε,
    existsi ε,
    split,
    assumption,
    intros,
    assumption
  end

end continuity

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
