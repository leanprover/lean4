/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
The real numbers, constructed as equivalence classes of Cauchy sequences of rationals.
This construction follows Bishop and Bridges (1985).

To do:
 o Rename things and possibly make theorems private
-/
import data.real.basic data.rat data.nat
open rat nat eq pnat

local postfix `⁻¹` := pnat.inv

namespace rat_seq
definition pos (s : seq) := ∃ n : ℕ+, n⁻¹ < (s n)

definition nonneg (s : seq) := ∀ n : ℕ+, -(n⁻¹) ≤ s n

theorem sub_sub_comm (a b c : ℚ) : a - b - c = a - c - b :=
  by rewrite [+sub_eq_add_neg, add.assoc, {-b+_}add.comm, -add.assoc]

theorem bdd_away_of_pos {s : seq} (Hs : regular s) (H : pos s) :
        ∃ N : ℕ+, ∀ n : ℕ+, n ≥ N → (s n) ≥ N⁻¹ :=
  begin
    cases H with [n, Hn],
    cases sep_by_inv Hn with [N, HN],
    existsi N,
    intro m Hm,
    have Habs : abs (s m - s n) ≥ s n - s m, by rewrite abs_sub; apply le_abs_self,
    have Habs' : s m + abs (s m - s n) ≥ s n, from (iff.mpr (le_add_iff_sub_left_le _ _ _)) Habs,
    have HN' : N⁻¹ + N⁻¹ ≤ s n - n⁻¹, begin
        rewrite sub_eq_add_neg,
        apply iff.mpr (le_add_iff_sub_right_le _ _ _),
        rewrite [sub_neg_eq_add, add.comm, -add.assoc],
        apply le_of_lt HN
      end,
    rewrite add.comm at Habs',
    have Hin : s m ≥ N⁻¹, from calc
      s m ≥ s n - abs (s m - s n) : (iff.mp (le_add_iff_sub_left_le _ _ _)) Habs'
      ... ≥ s n - (m⁻¹ + n⁻¹) : sub_le_sub_left !Hs
      ... = s n - m⁻¹ - n⁻¹ : by rewrite sub_add_eq_sub_sub
      ... = s n - n⁻¹ - m⁻¹ : by rewrite sub_sub_comm
      ... ≥ s n - n⁻¹ - N⁻¹ : sub_le_sub_left (inv_ge_of_le Hm)
      ... ≥ N⁻¹ + N⁻¹ - N⁻¹ : sub_le_sub_right HN'
      ... = N⁻¹ : by rewrite add_sub_cancel,
    apply Hin
  end

theorem pos_of_bdd_away {s : seq} (H : ∃ N : ℕ+, ∀ n : ℕ+, n ≥ N → (s n) ≥ N⁻¹) : pos s :=
  begin
    cases H with [N, HN],
    existsi (N + pone),
    apply lt_of_lt_of_le,
    apply inv_add_lt_left,
    apply HN,
    apply pnat.le_of_lt,
    apply lt_add_left
  end

theorem bdd_within_of_nonneg {s : seq} (Hs : regular s) (H : nonneg s) :
        ∀ n : ℕ+, ∃ N : ℕ+, ∀ m : ℕ+, m ≥ N → s m ≥ -n⁻¹ :=
  begin
    intros,
    existsi n,
    intro m Hm,
    apply le.trans,
    apply neg_le_neg,
    apply inv_ge_of_le,
    apply Hm,
    apply H
  end

theorem nonneg_of_bdd_within {s : seq} (Hs : regular s)
        (H : ∀n : ℕ+, ∃ N : ℕ+, ∀ m : ℕ+, m ≥ N → s m ≥ -n⁻¹) : nonneg s :=
  begin
    rewrite ↑nonneg,
    intro k,
    apply ge_of_forall_ge_sub,
    intro ε Hε,
    cases H (pceil ((2) / ε)) with [N, HN],
    apply le.trans,
    rotate 1,
    apply sub_le_of_abs_sub_le_left,
    apply Hs,
    apply (max (pceil ((2)/ε)) N),
    rewrite [+sub_eq_add_neg, neg_add, {_ + (-k⁻¹ + _)}add.comm, *add.assoc],
    apply rat.add_le_add_left,
    apply le.trans,
    rotate 1,
    apply add_le_add,
    rotate 1,
    apply HN (max (pceil ((2)/ε)) N) !pnat.max_right,
    rotate_right 1,
    apply neg_le_neg,
    apply inv_ge_of_le,
    apply pnat.max_left,
    rewrite -neg_add,
    apply neg_le_neg,
    apply le.trans,
    apply add_le_add,
    repeat (apply inv_pceil_div;
    apply add_pos;
    repeat apply zero_lt_one;
    exact Hε),
    rewrite [add_halves],
    apply rat.le_refl
  end

theorem pos_of_pos_equiv {s t : seq} (Hs : regular s) (Heq : s ≡ t) (Hp : pos s) : pos t :=
  begin
    cases (bdd_away_of_pos Hs Hp) with [N, HN],
    existsi 2 * 2 * N,
    apply lt_of_lt_of_le,
    rotate 1,
    apply sub_le_of_abs_sub_le_right,
    apply Heq,
    have Hs4 : N⁻¹ ≤ s (2 * 2 * N), from HN _ (!pnat.mul_le_mul_left),
    apply lt_of_lt_of_le,
    rotate 1,
    rewrite sub_eq_add_neg,
    apply iff.mpr !add_le_add_right_iff,
    apply Hs4,
    rewrite [*pnat.mul_assoc, pnat.add_halves, -(pnat.add_halves N), -sub_eq_add_neg, add_sub_cancel],
    apply inv_two_mul_lt_inv
  end

theorem nonneg_of_nonneg_equiv {s t : seq} (Hs : regular s) (Ht : regular t) (Heq : s ≡ t)
        (Hp : nonneg s) : nonneg t :=
  begin
    apply nonneg_of_bdd_within,
    apply Ht,
    intros,
    cases bdd_within_of_nonneg Hs Hp (2 * 2 * n) with [Ns, HNs],
    existsi max Ns (2 * 2 * n),
    intro m Hm,
    apply le.trans,
    rotate 1,
    apply sub_le_of_abs_sub_le_right,
    apply Heq,
    apply le.trans,
    rotate 1,
    apply sub_le_sub_right,
    apply HNs,
    apply pnat.le_trans,
    rotate 1,
    apply Hm,
    rotate_right 1,
    apply pnat.max_left,
    have Hms : m⁻¹ ≤ (2 * 2 * n)⁻¹, begin
         apply inv_ge_of_le,
         apply pnat.le_trans,
         rotate 1,
         apply Hm;
         apply pnat.max_right
      end,
    have Hms' : m⁻¹ + m⁻¹ ≤ (2 * 2 * n)⁻¹ + (2 * 2 * n)⁻¹, from add_le_add Hms Hms,
    apply le.trans,
    rotate 1,
    apply sub_le_sub_left,
    apply Hms',
    rewrite [*pnat.mul_assoc, pnat.add_halves, -neg_sub, -pnat.add_halves n, sub_neg_eq_add],
    apply neg_le_neg,
    apply add_le_add_left,
    apply inv_two_mul_le_inv
  end

definition s_le (a b : seq) := nonneg (sadd b (sneg a))
definition s_lt (a b : seq) := pos (sadd b (sneg a))

theorem zero_nonneg : nonneg zero :=
  begin
    intros,
    apply neg_nonpos_of_nonneg,
    apply rat.le_of_lt,
    apply pnat.inv_pos
  end

theorem s_zero_lt_one : s_lt zero one :=
  begin
    rewrite [↑s_lt, ↑zero, ↑sadd, ↑sneg, ↑one, neg_zero, add_zero, ↑pos],
    existsi 2,
    apply inv_lt_one_of_gt,
    apply one_lt_two
  end

protected theorem le_refl {s : seq} (Hs : regular s) : s_le s s :=
  begin
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply equiv.symm,
    apply neg_s_cancel s Hs,
    apply zero_nonneg,
    apply zero_is_reg,
    apply reg_add_reg Hs (reg_neg_reg Hs)
  end

theorem s_nonneg_of_pos {s : seq} (Hs : regular s) (H : pos s) : nonneg s :=
  begin
    apply nonneg_of_bdd_within,
    apply Hs,
    intros,
    cases bdd_away_of_pos Hs H with [N, HN],
    existsi N,
    intro m Hm,
    apply le.trans,
    rotate 1,
    apply HN,
    apply Hm,
    apply le.trans,
    rotate 1,
    apply rat.le_of_lt,
    apply pnat.inv_pos,
    rewrite -neg_zero,
    apply neg_le_neg,
    apply rat.le_of_lt,
    apply pnat.inv_pos
  end

theorem s_le_of_s_lt {s t : seq} (Hs : regular s) (Ht : regular t) (H : s_lt s t) : s_le s t :=
  begin
    rewrite [↑s_le, ↑s_lt at *],
    apply s_nonneg_of_pos,
    repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
  end

theorem s_neg_add_eq_s_add_neg (s t : seq) : sneg (sadd s t) ≡ sadd (sneg s) (sneg t) :=
  begin
    rewrite [↑equiv, ↑sadd, ↑sneg],
    intros,
    rewrite [neg_add, sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem equiv_cancel_middle {s t u : seq} (Hs : regular s) (Ht : regular t)
        (Hu : regular u) : sadd (sadd u t) (sneg (sadd u s)) ≡ sadd t (sneg s) :=
  begin
    note Hz := zero_is_reg,
    apply equiv.trans,
    rotate 3,
    apply add_well_defined,
    rotate 4,
    apply s_add_comm,
    apply s_neg_add_eq_s_add_neg,
    apply equiv.trans,
    rotate 3,
    apply s_add_assoc,
    rotate 2,
    apply add_well_defined,
    rotate 4,
    apply equiv.refl,
    apply equiv.trans,
    rotate 4,
    apply equiv.refl,
    rotate_right 1,
    apply equiv.trans,
    rotate 3,
    apply equiv.symm,
    apply s_add_assoc,
    rotate 2,
    apply equiv.trans,
    rotate 4,
    apply s_zero_add,
    rotate_right 1,
    apply add_well_defined,
    rotate 4,
    apply neg_s_cancel,
    rotate 1,
    apply equiv.refl,
    repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
  end

protected theorem add_le_add_of_le_right {s t : seq} (Hs : regular s) (Ht : regular t)
          (Lst : s_le s t) : ∀ u : seq, regular u → s_le (sadd u s) (sadd u t) :=
  begin
    intro u Hu,
    rewrite [↑s_le at *],
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply equiv.symm,
    apply equiv_cancel_middle,
    repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
  end

theorem s_add_lt_add_left {s t : seq} (Hs : regular s) (Ht : regular t) (Hst : s_lt s t) {u : seq}
        (Hu : regular u) : s_lt (sadd u s) (sadd u t) :=
  begin
    rewrite ↑s_lt at *,
    apply pos_of_pos_equiv,
    rotate 1,
    apply equiv.symm,
    apply equiv_cancel_middle,
    repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
  end

protected theorem add_nonneg_of_nonneg {s t : seq} (Hs : nonneg s) (Ht : nonneg t) :
          nonneg (sadd s t) :=
  begin
    intros,
    rewrite [-pnat.add_halves, neg_add],
    apply add_le_add,
    apply Hs,
    apply Ht
  end

protected theorem le_trans {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
          (Lst : s_le s t) (Ltu : s_le t u) : s_le s u :=
  begin
    rewrite ↑s_le at *,
    note Rz := zero_is_reg,
    have Hsum : nonneg (sadd (sadd u (sneg t)) (sadd t (sneg s))),
                from rat_seq.add_nonneg_of_nonneg Ltu Lst,
    have H' : nonneg (sadd (sadd u (sadd (sneg t) t)) (sneg s)), begin
      apply nonneg_of_nonneg_equiv,
      rotate 2,
      apply add_well_defined,
      rotate 4,
      apply s_add_assoc,
      repeat (apply reg_add_reg | apply reg_neg_reg | assumption),
      apply equiv.refl,
      apply nonneg_of_nonneg_equiv,
      rotate 2,
      apply equiv.symm,
      apply s_add_assoc,
      rotate 2,
      repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
    end,
    have H'' : sadd (sadd u (sadd (sneg t) t)) (sneg s) ≡ sadd u (sneg s), begin
      apply add_well_defined,
      rotate 4,
      apply equiv.trans,
      rotate 3,
      apply add_well_defined,
      rotate 4,
      apply equiv.refl,
      apply s_neg_cancel,
      rotate 1,
      apply s_add_zero,
      rotate 1,
      apply equiv.refl,
      repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
    end,
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply H'',
    apply H',
    repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
  end

theorem equiv_of_le_of_ge {s t : seq} (Hs : regular s) (Ht : regular t) (Lst : s_le s t)
        (Lts : s_le t s) : s ≡ t :=
  begin
    apply equiv_of_diff_equiv_zero,
    rotate 2,
    rewrite [↑s_le at *, ↑nonneg at *, ↑equiv, ↑sadd at *, ↑sneg at *],
    intros,
    rewrite [↑zero, sub_zero],
    apply abs_le_of_le_of_neg_le,
    apply le_of_neg_le_neg,
    rewrite [2 neg_add, neg_neg],
    apply rat.le_trans,
    apply neg_add_neg_le_neg_of_pos,
    apply pnat.inv_pos,
    rewrite add.comm,
    apply Lst,
    apply le_of_neg_le_neg,
    rewrite [neg_add, neg_neg],
    apply rat.le_trans,
    apply neg_add_neg_le_neg_of_pos,
    apply pnat.inv_pos,
    apply Lts,
    repeat assumption
  end

definition sep (s t : seq) := s_lt s t ∨ s_lt t s
local infix `≢` : 50 := sep

theorem le_and_sep_of_lt {s t : seq} (Hs : regular s) (Ht : regular t) (Lst : s_lt s t) :
        s_le s t ∧ sep s t :=
  begin
    apply and.intro,
    intros,
    cases Lst with [N, HN],
    let Rns := reg_neg_reg Hs,
    let Rtns := reg_add_reg Ht Rns,
    note Habs := sub_le_of_abs_sub_le_right (Rtns N n),
    rewrite [sub_add_eq_sub_sub at Habs],
    exact (calc
      sadd t (sneg s) n ≥ sadd t (sneg s) N -  N⁻¹ - n⁻¹ : Habs
      ... ≥ 0 - n⁻¹: begin
                       apply sub_le_sub_right,
                       apply rat.le_of_lt,
                       apply (iff.mpr (sub_pos_iff_lt _ _)),
                       apply HN
                     end
      ... = -n⁻¹ : by rewrite zero_sub),
    exact or.inl Lst
  end

theorem lt_of_le_and_sep {s t : seq} (Hs : regular s) (Ht : regular t) (H : s_le s t ∧ sep s t) :
        s_lt s t :=
  begin
    note Le := and.left H,
    cases and.right H with [P, Hlt],
    exact P,
    rewrite [↑s_le at Le, ↑nonneg at Le, ↑s_lt at Hlt, ↑pos at Hlt],
    apply exists.elim Hlt,
    intro N HN,
    let LeN := Le N,
    note HN' := (iff.mpr !neg_lt_neg_iff_lt) HN,
    rewrite [↑sadd at HN', ↑sneg at HN', neg_add at HN', neg_neg at HN', add.comm at HN'],
    let HN'' := not_le_of_gt HN',
    apply absurd LeN HN''
  end

theorem lt_iff_le_and_sep {s t : seq} (Hs : regular s) (Ht : regular t) :
        s_lt s t ↔ s_le s t ∧ sep s t :=
  iff.intro (le_and_sep_of_lt Hs Ht) (lt_of_le_and_sep Hs Ht)

theorem s_neg_zero : sneg zero ≡ zero :=
  begin
    rewrite ↑[sneg, zero, equiv],
    intros,
    rewrite [sub_zero, abs_neg, abs_zero],
    apply add_invs_nonneg
  end

theorem s_sub_zero {s : seq} (Hs : regular s) : sadd s (sneg zero) ≡ s :=
  begin
    apply equiv.trans,
    rotate 3,
    apply add_well_defined,
    rotate 4,
    apply equiv.refl,
    apply s_neg_zero,
    apply s_add_zero,
    repeat (assumption | apply reg_add_reg | apply reg_neg_reg | apply zero_is_reg)
  end

theorem s_pos_of_gt_zero {s : seq} (Hs : regular s) (Hgz : s_lt zero s) : pos s :=
  begin
    rewrite [↑s_lt at *],
    apply pos_of_pos_equiv,
    rotate 1,
    apply s_sub_zero,
    repeat (assumption | apply reg_add_reg | apply reg_neg_reg),
    apply zero_is_reg
  end

theorem s_gt_zero_of_pos {s : seq} (Hs : regular s) (Hp : pos s) : s_lt zero s :=
  begin
    rewrite ↑s_lt,
    apply pos_of_pos_equiv,
    rotate 1,
    apply equiv.symm,
    apply s_sub_zero,
    repeat assumption
  end

theorem s_nonneg_of_ge_zero {s : seq} (Hs : regular s) (Hgz : s_le zero s) : nonneg s :=
  begin
    rewrite ↑s_le at *,
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply s_sub_zero,
    repeat (assumption | apply reg_add_reg | apply reg_neg_reg | apply zero_is_reg)
  end

theorem s_ge_zero_of_nonneg {s : seq} (Hs : regular s) (Hn : nonneg s) : s_le zero s :=
  begin
    rewrite ↑s_le,
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply equiv.symm,
    apply s_sub_zero,
    repeat (assumption | apply reg_add_reg | apply reg_neg_reg | apply zero_is_reg)
  end

theorem s_mul_pos_of_pos {s t : seq} (Hs : regular s) (Ht : regular t) (Hps : pos s)
        (Hpt : pos t) : pos (smul s t) :=
  begin
    rewrite [↑pos at *],
    cases bdd_away_of_pos Hs Hps with [Ns, HNs],
    cases bdd_away_of_pos Ht Hpt with [Nt, HNt],
    existsi 2 * max Ns Nt * max Ns Nt,
    rewrite ↑smul,
    apply lt_of_lt_of_le,
    rotate 1,
    apply mul_le_mul,
    apply HNs,
    apply pnat.le_trans,
    apply pnat.max_left Ns Nt,
    rewrite -pnat.mul_assoc,
    apply pnat.mul_le_mul_left,
    apply HNt,
    apply pnat.le_trans,
    apply pnat.max_right Ns Nt,
    rewrite -pnat.mul_assoc,
    apply pnat.mul_le_mul_left,
    apply rat.le_of_lt,
    apply pnat.inv_pos,
    apply rat.le_trans,
    rotate 1,
    apply HNs,
    apply pnat.le_trans,
    apply pnat.max_left Ns Nt,
    rewrite -pnat.mul_assoc,
    apply pnat.mul_le_mul_left,
    rewrite pnat.inv_mul_eq_mul_inv,
    apply mul_lt_mul,
    rewrite [pnat.inv_mul_eq_mul_inv, -one_mul Ns⁻¹],
    apply mul_lt_mul,
    apply inv_lt_one_of_gt,
    apply dec_trivial,
    apply inv_ge_of_le,
    apply pnat.max_left,
    apply pnat.inv_pos,
    apply rat.le_of_lt zero_lt_one,
    apply inv_ge_of_le,
    apply pnat.max_right,
    apply pnat.inv_pos,
    repeat (apply le_of_lt; apply pnat.inv_pos)
  end

theorem s_mul_gt_zero_of_gt_zero {s t : seq} (Hs : regular s) (Ht : regular t)
        (Hzs : s_lt zero s) (Hzt : s_lt zero t) : s_lt zero (smul s t) :=
  s_gt_zero_of_pos
    (reg_mul_reg Hs Ht)
    (s_mul_pos_of_pos Hs Ht (s_pos_of_gt_zero Hs Hzs) (s_pos_of_gt_zero Ht Hzt))

theorem le_of_lt_or_equiv {s t : seq} (Hs : regular s) (Ht : regular t)
        (Hor : (s_lt s t) ∨ (s ≡ t)) : s_le s t :=
  or.elim Hor
    (begin
      intro Hlt,
      apply s_le_of_s_lt Hs Ht Hlt
    end)
    (begin
      intro Heq,
      rewrite ↑s_le,
      apply nonneg_of_nonneg_equiv,
      rotate 3,
      apply zero_nonneg,
      apply zero_is_reg,
      apply reg_add_reg Ht (reg_neg_reg Hs),
      apply equiv.symm,
      apply diff_equiv_zero_of_equiv,
      rotate 2,
      apply equiv.symm,
      apply Heq,
      repeat assumption
    end)

theorem s_zero_mul {s : seq} : smul s zero ≡ zero :=
  begin
    rewrite [↑equiv, ↑smul, ↑zero],
    intros,
    rewrite [mul_zero, sub_zero, abs_zero],
    apply add_invs_nonneg
  end

theorem s_mul_nonneg_of_pos_of_zero {s t : seq} (Hs : regular s) (Ht : regular t)
       (Hps : pos s) (Hpt : zero ≡ t) : nonneg (smul s t) :=
  begin
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply mul_well_defined,
    rotate 4,
    apply equiv.refl,
    apply Hpt,
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply equiv.symm,
    apply s_zero_mul,
    apply zero_nonneg,
    repeat (assumption | apply reg_mul_reg | apply zero_is_reg)
  end

theorem s_mul_nonneg_of_nonneg {s t : seq} (Hs : regular s) (Ht : regular t)
        (Hps : nonneg s) (Hpt : nonneg t) : nonneg (smul s t) :=
  begin
    intro n,
    rewrite ↑smul,
    apply rat.le_by_cases 0 (s (((K₂ s t) * 2) * n)),
    intro Hsp,
    apply rat.le_by_cases 0 (t (((K₂ s t) * 2) * n)),
    intro Htp,
    apply rat.le_trans,
    rotate 1,
    apply rat.mul_nonneg Hsp Htp,
    rotate_right 1,
    apply le_of_lt,
    apply neg_neg_of_pos,
    apply pnat.inv_pos,
      intro Htn,
      apply rat.le_trans,
      rotate 1,
      apply mul_le_mul_of_nonpos_right,
      apply rat.le_trans,
      apply le_abs_self,
      apply canon_2_bound_left s t Hs,
      apply Htn,
      rotate_right 1,
      apply rat.le_trans,
      rotate 1,
      apply mul_le_mul_of_nonneg_left,
      apply Hpt,
      apply le_of_lt,
      apply rat_of_pnat_is_pos,
      rotate 1,
      rewrite -neg_mul_eq_mul_neg,
      apply neg_le_neg,
      rewrite [*pnat.mul_assoc, pnat.inv_mul_eq_mul_inv, -mul.assoc, pnat.inv_cancel_left, one_mul],
      apply inv_ge_of_le,
      apply pnat.mul_le_mul_left,
     intro Hsn,
     apply rat.le_by_cases 0 (t (((K₂ s t) * 2) * n)),
     intro Htp,
     apply rat.le_trans,
     rotate 1,
     apply mul_le_mul_of_nonpos_left,
     apply rat.le_trans,
     apply le_abs_self,
     apply canon_2_bound_right s t Ht,
     apply Hsn,
     rotate_right 1,
     apply rat.le_trans,
     rotate 1,
     apply mul_le_mul_of_nonneg_right,
     apply Hps,
     apply le_of_lt,
     apply rat_of_pnat_is_pos,
     rotate 1,
     rewrite -neg_mul_eq_neg_mul,
     apply neg_le_neg,
     rewrite [+pnat.mul_assoc, pnat.inv_mul_eq_mul_inv, mul.comm, -mul.assoc, pnat.inv_cancel_left,
             one_mul],
     apply inv_ge_of_le,
     apply pnat.mul_le_mul_left,
    intro Htn,
    apply le.trans,
    rotate 1,
    apply mul_nonneg_of_nonpos_of_nonpos,
    apply Hsn,
    apply Htn,
    apply le_of_lt,
    apply neg_neg_of_pos,
    apply pnat.inv_pos
  end

theorem s_mul_ge_zero_of_ge_zero {s t : seq} (Hs : regular s) (Ht : regular t)
        (Hzs : s_le zero s) (Hzt : s_le zero t) : s_le zero (smul s t) :=
  begin
    note Hzs' := s_nonneg_of_ge_zero Hs Hzs,
    note Htz' := s_nonneg_of_ge_zero Ht Hzt,
    apply s_ge_zero_of_nonneg,
    rotate 1,
    apply s_mul_nonneg_of_nonneg,
    repeat assumption,
    apply reg_mul_reg Hs Ht
  end

protected theorem not_lt_self (s : seq) : ¬ s_lt s s :=
  begin
    intro Hlt,
    rewrite [↑s_lt at Hlt, ↑pos at Hlt],
    apply exists.elim Hlt,
    intro n Hn, esimp at Hn,
    rewrite [↑sadd at Hn,↑sneg at Hn, -sub_eq_add_neg at Hn, sub_self at Hn],
    apply absurd Hn (not_lt_of_ge (rat.le_of_lt !pnat.inv_pos))
  end

theorem not_sep_self (s : seq) : ¬ s ≢ s :=
  begin
    intro Hsep,
    rewrite ↑sep at Hsep,
    let Hsep' := (iff.mp !or_self) Hsep,
    apply absurd Hsep' (!rat_seq.not_lt_self)
  end

theorem le_well_defined {s t u v : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Hv : regular v) (Hsu : s ≡ u) (Htv : t ≡ v) :  s_le s t ↔ s_le u v :=
  iff.intro
  (begin
    intro Hle,
    rewrite [↑s_le at *],
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply add_well_defined,
    rotate 4,
    apply Htv,
    apply neg_well_defined,
    apply Hsu,
    apply Hle,
    repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
  end)
  (begin
    intro Hle,
    rewrite [↑s_le at *],
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply add_well_defined,
    rotate 4,
    apply equiv.symm, apply Htv,
    apply neg_well_defined,
    apply equiv.symm, apply Hsu,
    apply Hle,
    repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
  end)

theorem lt_well_defined {s t u v : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Hv : regular v) (Hsu : s ≡ u) (Htv : t ≡ v) : s_lt s t ↔ s_lt u v :=
  iff.intro
  (begin
    intro Hle,
    rewrite [↑s_lt at *],
    apply pos_of_pos_equiv,
    rotate 1,
    apply add_well_defined,
    rotate 4,
    apply Htv,
    apply neg_well_defined,
    apply Hsu,
    apply Hle,
    repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
  end)
  (begin
    intro Hle,
    rewrite [↑s_lt at *],
    apply pos_of_pos_equiv,
    rotate 1,
    apply add_well_defined,
    rotate 4,
    apply equiv.symm, apply Htv,
    apply neg_well_defined,
    apply equiv.symm, apply Hsu,
    apply Hle,
    repeat (apply reg_add_reg | apply reg_neg_reg | assumption)
  end)

theorem sep_well_defined {s t u v : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Hv : regular v) (Hsu : s ≡ u) (Htv : t ≡ v) : s ≢ t ↔ u ≢ v :=
  begin
    rewrite ↑sep,
    apply iff.intro,
    intro Hor,
    apply or.elim Hor,
    intro Hlt,
    apply or.inl,
    apply iff.mp (lt_well_defined Hs Ht Hu Hv Hsu Htv),
    assumption,
    intro Hlt,
    apply or.inr,
    apply iff.mp (lt_well_defined Ht Hs Hv Hu Htv Hsu),
    assumption,
    intro Hor,
    apply or.elim Hor,
    intro Hlt,
    apply or.inl,
    apply iff.mpr (lt_well_defined Hs Ht Hu Hv Hsu Htv),
    assumption,
    intro Hlt,
    apply or.inr,
    apply iff.mpr (lt_well_defined Ht Hs Hv Hu Htv Hsu),
    assumption
  end

theorem s_lt_of_lt_of_le {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Hst : s_lt s t) (Htu : s_le t u) : s_lt s u :=
  begin
    let Rtns := reg_add_reg Ht (reg_neg_reg Hs),
    let Runt := reg_add_reg Hu (reg_neg_reg Ht),
    have Hcan : ∀ m, sadd u (sneg s) m = (sadd t (sneg s)) m + (sadd u (sneg t)) m, begin
      intro m,
      rewrite [↑sadd, ↑sneg, -*sub_eq_add_neg, -sub_eq_sub_add_sub]
    end,
    rewrite [↑s_lt at *, ↑s_le at *],
    cases bdd_away_of_pos Rtns Hst with [Nt, HNt],
    cases bdd_within_of_nonneg Runt Htu (2 * Nt) with [Nu, HNu],
    apply pos_of_bdd_away,
    existsi max (2 * Nt) Nu,
    intro n Hn,
    rewrite Hcan,
    apply rat.le_trans,
    rotate 1,
    apply add_le_add,
    apply HNt,
    apply pnat.le_trans,
    apply pnat.mul_le_mul_left 2,
    apply pnat.le_trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply pnat.max_left,
    apply HNu,
    apply pnat.le_trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply pnat.max_right,
    rewrite [-pnat.add_halves Nt, -sub_eq_add_neg, add_sub_cancel],
    apply inv_ge_of_le,
    apply pnat.max_left
  end

theorem s_lt_of_le_of_lt {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Hst : s_le s t) (Htu : s_lt t u) : s_lt s u :=
  begin
    let Rtns := reg_add_reg Ht (reg_neg_reg Hs),
    let Runt := reg_add_reg Hu (reg_neg_reg Ht),
    have Hcan : ∀ m, sadd u (sneg s) m = (sadd t (sneg s)) m + (sadd u (sneg t)) m, begin
      intro m,
      rewrite [↑sadd, ↑sneg, -*sub_eq_add_neg, -sub_eq_sub_add_sub]
    end,
    rewrite [↑s_lt at *, ↑s_le at *],
    cases bdd_away_of_pos Runt Htu with [Nu, HNu],
    cases bdd_within_of_nonneg Rtns Hst (2 * Nu) with [Nt, HNt],
    apply pos_of_bdd_away,
    existsi max (2 * Nu) Nt,
    intro n Hn,
    rewrite Hcan,
    apply rat.le_trans,
    rotate 1,
    apply add_le_add,
    apply HNt,
    apply pnat.le_trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply pnat.max_right,
    apply HNu,
    apply pnat.le_trans,
    apply pnat.mul_le_mul_left 2,
    apply pnat.le_trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply pnat.max_left,
    rewrite [-pnat.add_halves Nu, neg_add_cancel_left],
    apply inv_ge_of_le,
    apply pnat.max_left
  end

theorem le_of_le_reprs {s t : seq} (Hs : regular s) (Ht : regular t)
        (Hle : ∀ n : ℕ+, s_le s (const (t n))) : s_le s t :=
  by intro m; apply Hle (2 * m) m

theorem le_of_reprs_le {s t : seq} (Hs : regular s) (Ht : regular t)
        (Hle : ∀ n : ℕ+, s_le (const (t n)) s) : s_le t s :=
  by intro m; apply Hle (2 * m) m

-----------------------------
-- of_rat theorems

theorem const_le_const_of_le {a b : ℚ} (H : a ≤ b) : s_le (const a) (const b) :=
  begin
    rewrite [↑s_le, ↑nonneg],
    intro n,
    rewrite [↑sadd, ↑sneg, ↑const],
    apply le.trans,
    apply neg_nonpos_of_nonneg,
    apply rat.le_of_lt,
    apply pnat.inv_pos,
    apply iff.mpr !sub_nonneg_iff_le,
    apply H
  end

theorem le_of_const_le_const {a b : ℚ} (H : s_le (const a) (const b)) : a ≤ b :=
  begin
    rewrite [↑s_le at H, ↑nonneg at H, ↑sadd at H, ↑sneg at H, ↑const at H],
    apply iff.mp !sub_nonneg_iff_le,
    apply nonneg_of_ge_neg_invs _ H
  end

theorem nat_inv_lt_rat {a : ℚ} (H : a > 0) : ∃ n : ℕ+, n⁻¹ < a :=
  begin
    existsi (pceil (1 / (a / (2)))),
    apply lt_of_le_of_lt,
    rotate 1,
    apply div_two_lt_of_pos H,
    rewrite -(one_div_one_div (a / (1 + 1))),
    apply pceil_helper,
    apply pnat.le_refl,
    apply one_div_pos_of_pos,
    apply div_pos_of_pos_of_pos H dec_trivial
  end


theorem const_lt_const_of_lt {a b : ℚ} (H : a < b) : s_lt (const a) (const b) :=
  begin
    rewrite [↑s_lt, ↑pos, ↑sadd, ↑sneg, ↑const],
    apply nat_inv_lt_rat,
    apply (iff.mpr !sub_pos_iff_lt H)
  end

theorem lt_of_const_lt_const {a b : ℚ} (H : s_lt (const a) (const b)) : a < b :=
  begin
    rewrite [↑s_lt at H, ↑pos at H, ↑const at H, ↑sadd at H, ↑sneg at H],
    cases H with [n, Hn],
    apply (iff.mp !sub_pos_iff_lt),
    apply lt.trans,
    rotate 1,
    exact Hn,
    apply pnat.inv_pos
  end

theorem s_le_of_le_pointwise {s t : seq} (Hs : regular s) (Ht : regular t)
        (H : ∀ n : ℕ+, s n ≤ t n) : s_le s t :=
  begin
    rewrite [↑s_le, ↑nonneg, ↑sadd, ↑sneg],
    intros,
    apply le.trans,
    apply iff.mpr !neg_nonpos_iff_nonneg,
    apply le_of_lt,
    apply pnat.inv_pos,
    apply iff.mpr !sub_nonneg_iff_le,
    apply H
  end

-------- lift to reg_seqs
definition r_lt (s t : reg_seq) := s_lt (reg_seq.sq s) (reg_seq.sq t)
definition r_le (s t : reg_seq) := s_le (reg_seq.sq s) (reg_seq.sq t)
definition r_sep (s t : reg_seq) := sep (reg_seq.sq s) (reg_seq.sq t)

theorem r_le_well_defined (s t u v : reg_seq) (Hsu : requiv s u) (Htv : requiv t v)
        : r_le s t = r_le u v :=
  propext (le_well_defined (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u)
                  (reg_seq.is_reg v) Hsu Htv)


theorem r_lt_well_defined (s t u v : reg_seq) (Hsu : requiv s u) (Htv : requiv t v)
        : r_lt s t = r_lt u v :=
  propext (lt_well_defined (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u)
                  (reg_seq.is_reg v) Hsu Htv)

theorem r_sep_well_defined (s t u v : reg_seq) (Hsu : requiv s u) (Htv : requiv t v)
        : r_sep s t = r_sep u v :=
  propext (sep_well_defined (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u)
                  (reg_seq.is_reg v) Hsu Htv)

theorem r_le.refl (s : reg_seq) : r_le s s := rat_seq.le_refl (reg_seq.is_reg s)

theorem r_le.trans {s t u : reg_seq} (Hst : r_le s t) (Htu : r_le t u) : r_le s u :=
  rat_seq.le_trans (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u) Hst Htu

theorem r_equiv_of_le_of_ge {s t : reg_seq} (Hs : r_le s t) (Hu : r_le t s) :
        requiv s t :=
  equiv_of_le_of_ge (reg_seq.is_reg s) (reg_seq.is_reg t) Hs Hu

theorem r_lt_iff_le_and_sep (s t : reg_seq) : r_lt s t ↔ r_le s t ∧ r_sep s t :=
  lt_iff_le_and_sep (reg_seq.is_reg s) (reg_seq.is_reg t)

theorem r_add_le_add_of_le_right {s t : reg_seq} (H : r_le s t) (u : reg_seq) :
        r_le (u + s) (u + t) :=
  rat_seq.add_le_add_of_le_right (reg_seq.is_reg s) (reg_seq.is_reg t) H
                                        (reg_seq.sq u) (reg_seq.is_reg u)

theorem r_add_le_add_of_le_right_var (s t u : reg_seq) (H : r_le s t) :
        r_le (u + s) (u + t) := r_add_le_add_of_le_right H u

theorem r_mul_pos_of_pos {s t : reg_seq} (Hs : r_lt r_zero s) (Ht : r_lt r_zero t) :
        r_lt r_zero (s * t) :=
  s_mul_gt_zero_of_gt_zero (reg_seq.is_reg s) (reg_seq.is_reg t) Hs Ht

theorem r_mul_nonneg_of_nonneg {s t : reg_seq} (Hs : r_le r_zero s) (Ht : r_le r_zero t) :
        r_le r_zero (s * t) :=
  s_mul_ge_zero_of_ge_zero (reg_seq.is_reg s) (reg_seq.is_reg t) Hs Ht

theorem r_not_lt_self (s : reg_seq) : ¬ r_lt s s :=
  rat_seq.not_lt_self (reg_seq.sq s)

theorem r_not_sep_self (s : reg_seq) : ¬ r_sep s s :=
  not_sep_self (reg_seq.sq s)

theorem r_le_of_lt {s t : reg_seq} (H : r_lt s t) : r_le s t :=
  s_le_of_s_lt (reg_seq.is_reg s) (reg_seq.is_reg t) H

theorem r_lt_of_le_of_lt {s t u : reg_seq} (Hst : r_le s t) (Htu : r_lt t u) : r_lt s u :=
  s_lt_of_le_of_lt (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u) Hst Htu

theorem r_lt_of_lt_of_le {s t u : reg_seq} (Hst : r_lt s t) (Htu : r_le t u) : r_lt s u :=
  s_lt_of_lt_of_le (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u) Hst Htu

theorem r_add_lt_add_left (s t : reg_seq) (H : r_lt s t) (u : reg_seq) : r_lt (u + s) (u + t) :=
  s_add_lt_add_left (reg_seq.is_reg s) (reg_seq.is_reg t) H (reg_seq.is_reg u)

theorem r_add_lt_add_left_var (s t u : reg_seq) (H : r_lt s t) : r_lt (u + s) (u + t) :=
  r_add_lt_add_left s t H u

theorem r_zero_lt_one : r_lt r_zero r_one := s_zero_lt_one

theorem r_le_of_lt_or_eq (s t : reg_seq) (H : r_lt s t ∨ requiv s t) : r_le s t :=
  le_of_lt_or_equiv (reg_seq.is_reg s) (reg_seq.is_reg t) H

theorem r_const_le_const_of_le {a b : ℚ} (H : a ≤ b) : r_le (r_const a) (r_const b) :=
  const_le_const_of_le H

theorem r_le_of_const_le_const {a b : ℚ} (H : r_le (r_const a) (r_const b)) : a ≤ b :=
  le_of_const_le_const H

theorem r_const_lt_const_of_lt {a b : ℚ} (H : a < b) : r_lt (r_const a) (r_const b) :=
  const_lt_const_of_lt H

theorem r_lt_of_const_lt_const {a b : ℚ} (H : r_lt (r_const a) (r_const b)) : a < b :=
  lt_of_const_lt_const H

theorem r_le_of_le_reprs (s t : reg_seq) (Hle : ∀ n : ℕ+, r_le s (r_const (reg_seq.sq t n))) : r_le s t :=
  le_of_le_reprs (reg_seq.is_reg s) (reg_seq.is_reg t) Hle

theorem r_le_of_reprs_le (s t : reg_seq) (Hle : ∀ n : ℕ+, r_le (r_const (reg_seq.sq t n)) s) :
        r_le t s :=
  le_of_reprs_le (reg_seq.is_reg s) (reg_seq.is_reg t) Hle

end rat_seq

open real
open [class] rat_seq
namespace real

protected definition lt (x y : ℝ) :=
  quot.lift_on₂ x y (λ a b, rat_seq.r_lt a b) rat_seq.r_lt_well_defined
protected definition le (x y : ℝ) :=
  quot.lift_on₂ x y (λ a b, rat_seq.r_le a b) rat_seq.r_le_well_defined

definition real_has_lt [reducible] [instance] [priority real.prio] : has_lt ℝ :=
has_lt.mk real.lt

definition real_has_le [reducible] [instance] [priority real.prio] : has_le ℝ :=
has_le.mk real.le

definition sep (x y : ℝ) := quot.lift_on₂ x y (λ a b, rat_seq.r_sep a b) rat_seq.r_sep_well_defined
infix `≢` : 50 := sep

protected theorem le_refl (x : ℝ) : x ≤ x :=
  quot.induction_on x (λ t, rat_seq.r_le.refl t)

protected theorem le_trans {x y z : ℝ} : x ≤ y → y ≤ z → x ≤ z :=
  quot.induction_on₃ x y z (λ s t u, rat_seq.r_le.trans)

protected theorem eq_of_le_of_ge {x y : ℝ} : x ≤ y → y ≤ x → x = y :=
  quot.induction_on₂ x y (λ s t Hst Hts, quot.sound (rat_seq.r_equiv_of_le_of_ge Hst Hts))

theorem lt_iff_le_and_sep (x y : ℝ) : x < y ↔ x ≤ y ∧ x ≢ y :=
  quot.induction_on₂ x y (λ s t, rat_seq.r_lt_iff_le_and_sep s t)

protected theorem add_le_add_left' (x y z : ℝ) : x ≤ y → z + x ≤ z + y :=
  quot.induction_on₃ x y z (λ s t u, rat_seq.r_add_le_add_of_le_right_var s t u)

protected theorem add_le_add_left (x y : ℝ) : x ≤ y → ∀ z : ℝ, z + x ≤ z + y :=
  take H z, real.add_le_add_left' x y z H

protected theorem mul_pos (x y : ℝ) : 0 < x → 0 < y → 0 < x * y :=
  quot.induction_on₂ x y (λ s t, rat_seq.r_mul_pos_of_pos)

protected theorem mul_nonneg (x y : ℝ) : 0 ≤ x → 0 ≤ y → 0 ≤ x * y :=
  quot.induction_on₂ x y (λ s t, rat_seq.r_mul_nonneg_of_nonneg)

theorem not_sep_self (x : ℝ) : ¬ x ≢ x :=
  quot.induction_on x (λ s, rat_seq.r_not_sep_self s)

protected theorem lt_irrefl (x : ℝ) : ¬ x < x :=
  quot.induction_on x (λ s, rat_seq.r_not_lt_self s)

protected theorem le_of_lt {x y : ℝ} : x < y → x ≤ y :=
  quot.induction_on₂ x y (λ s t H', rat_seq.r_le_of_lt H')

protected theorem lt_of_le_of_lt {x y z : ℝ} : x ≤ y → y < z → x < z :=
  quot.induction_on₃ x y z (λ s t u H H', rat_seq.r_lt_of_le_of_lt H H')

protected theorem lt_of_lt_of_le {x y z : ℝ} : x < y → y ≤ z → x < z :=
  quot.induction_on₃ x y z (λ s t u H H', rat_seq.r_lt_of_lt_of_le H H')

protected theorem add_lt_add_left' (x y z : ℝ) : x < y → z + x < z + y :=
  quot.induction_on₃ x y z (λ s t u, rat_seq.r_add_lt_add_left_var s t u)

protected theorem add_lt_add_left (x y : ℝ) : x < y → ∀ z : ℝ, z + x < z + y :=
  take H z, real.add_lt_add_left' x y z H

protected theorem zero_lt_one : (0 : ℝ) < (1 : ℝ) := rat_seq.r_zero_lt_one

protected theorem le_of_lt_or_eq (x y : ℝ) : x < y ∨ x = y → x ≤ y :=
    (quot.induction_on₂ x y (λ s t H, or.elim H (take H', begin
        apply rat_seq.r_le_of_lt_or_eq,
        apply or.inl H'
      end)
      (take H', begin
        apply rat_seq.r_le_of_lt_or_eq,
        apply (or.inr (quot.exact H'))
      end)))

definition ordered_ring [reducible] [instance] : ordered_ring ℝ :=
⦃ ordered_ring, real.comm_ring,
  le_refl := real.le_refl,
  le_trans := @real.le_trans,
  mul_pos := real.mul_pos,
  mul_nonneg := real.mul_nonneg,
  zero_ne_one := real.zero_ne_one,
  add_le_add_left := real.add_le_add_left,
  le_antisymm := @real.eq_of_le_of_ge,
  lt_irrefl := real.lt_irrefl,
  lt_of_le_of_lt := @real.lt_of_le_of_lt,
  lt_of_lt_of_le := @real.lt_of_lt_of_le,
  le_of_lt := @real.le_of_lt,
  add_lt_add_left := real.add_lt_add_left
⦄

open int
theorem of_rat_sub (a b : ℚ) : of_rat (a - b) = of_rat a - of_rat b := rfl

theorem of_int_sub (a b : ℤ) : of_int (a - b) = of_int a - of_int b :=
  by rewrite [of_int_eq, rat.of_int_sub, of_rat_sub]

theorem of_rat_le_of_rat_of_le {a b : ℚ} : a ≤ b → of_rat a ≤ of_rat b :=
  rat_seq.r_const_le_const_of_le

theorem le_of_of_rat_le_of_rat {a b : ℚ} : of_rat a ≤ of_rat b → a ≤ b :=
  rat_seq.r_le_of_const_le_const

theorem of_rat_le_of_rat_iff (a b : ℚ) : of_rat a ≤ of_rat b ↔ a ≤ b :=
  iff.intro le_of_of_rat_le_of_rat of_rat_le_of_rat_of_le

theorem of_rat_lt_of_rat_of_lt {a b : ℚ} : a < b → of_rat a < of_rat b :=
  rat_seq.r_const_lt_const_of_lt

theorem lt_of_of_rat_lt_of_rat {a b : ℚ} : of_rat a < of_rat b → a < b :=
  rat_seq.r_lt_of_const_lt_const

theorem of_rat_lt_of_rat_iff (a b : ℚ) : of_rat a < of_rat b ↔ a < b :=
  iff.intro lt_of_of_rat_lt_of_rat of_rat_lt_of_rat_of_lt

theorem of_int_le_of_int_iff (a b : ℤ) : of_int a ≤ of_int b ↔ (a ≤ b) :=
  begin rewrite [+of_int_eq, of_rat_le_of_rat_iff], apply rat.of_int_le_of_int_iff end

theorem of_int_le_of_int_of_le {a b : ℤ} : (a ≤ b) → of_int a ≤ of_int b :=
  iff.mpr !of_int_le_of_int_iff

theorem le_of_of_int_le_of_int {a b : ℤ} : of_int a ≤ of_int b → (a ≤ b) :=
  iff.mp !of_int_le_of_int_iff

theorem of_int_lt_of_int_iff (a b : ℤ) : of_int a < of_int b ↔ (a < b) :=
  by rewrite [*of_int_eq, of_rat_lt_of_rat_iff]; apply rat.of_int_lt_of_int_iff

theorem of_int_lt_of_int_of_lt {a b : ℤ} : (a < b) → of_int a < of_int b :=
  iff.mpr !of_int_lt_of_int_iff

theorem lt_of_of_int_lt_of_int {a b : ℤ} : of_int a < of_int b → (a < b) :=
  iff.mp !of_int_lt_of_int_iff

theorem of_nat_le_of_nat_iff (a b : ℕ) : of_nat a ≤ of_nat b ↔ (a ≤ b) :=
  by rewrite [*of_nat_eq, of_rat_le_of_rat_iff]; apply rat.of_nat_le_of_nat_iff

theorem of_nat_le_of_nat_of_le {a b : ℕ} : (a ≤ b) → of_nat a ≤ of_nat b :=
  iff.mpr !of_nat_le_of_nat_iff

theorem le_of_of_nat_le_of_nat {a b : ℕ} : of_nat a ≤ of_nat b → (a ≤ b) :=
  iff.mp !of_nat_le_of_nat_iff

theorem of_nat_lt_of_nat_iff (a b : ℕ) : of_nat a < of_nat b ↔ (a < b) :=
  by rewrite [*of_nat_eq, of_rat_lt_of_rat_iff]; apply rat.of_nat_lt_of_nat_iff

theorem of_nat_lt_of_nat_of_lt {a b : ℕ} : (a < b) → of_nat a < of_nat b :=
  iff.mpr !of_nat_lt_of_nat_iff

theorem lt_of_of_nat_lt_of_nat {a b : ℕ} : of_nat a < of_nat b → (a < b) :=
  iff.mp !of_nat_lt_of_nat_iff

theorem of_rat_pos_of_pos {q : ℚ} (Hq : q > 0) : of_rat q > 0 :=
  of_rat_lt_of_rat_of_lt Hq

theorem of_rat_nonneg_of_nonneg {q : ℚ} (Hq : q ≥ 0) : of_rat q ≥ 0 :=
  of_rat_le_of_rat_of_le Hq

theorem of_rat_neg_of_neg {q : ℚ} (Hq : q < 0) : of_rat q < 0 :=
  of_rat_lt_of_rat_of_lt Hq

theorem of_rat_nonpos_of_nonpos {q : ℚ} (Hq : q ≤ 0) : of_rat q ≤ 0 :=
  of_rat_le_of_rat_of_le Hq

theorem of_nat_nonneg (a : ℕ) : of_nat a ≥ 0 :=
of_rat_le_of_rat_of_le !rat.of_nat_nonneg

theorem of_nat_succ_pos (k : ℕ) : 0 < of_nat k + 1 :=
  add_pos_of_nonneg_of_pos (of_nat_nonneg k) real.zero_lt_one

theorem of_rat_pow (a : ℚ) (n : ℕ) : of_rat (a^n) = (of_rat a)^n :=
begin
  induction n with n ih,
    apply eq.refl,
  rewrite [2 pow_succ, of_rat_mul, ih]
end

theorem of_int_pow (a : ℤ) (n : ℕ) : of_int (#int a^n) = (of_int a)^n :=
by rewrite [of_int_eq, rat.of_int_pow, of_rat_pow]

theorem of_nat_pow (a : ℕ) (n : ℕ) : of_nat (#nat a^n) = (of_nat a)^n :=
by rewrite [of_nat_eq, rat.of_nat_pow, of_rat_pow]

open rat_seq
theorem le_of_le_reprs (x : ℝ) (t : seq) (Ht : regular t) : (∀ n : ℕ+, x ≤ t n) →
        x ≤ quot.mk (reg_seq.mk t Ht) :=
  quot.induction_on x (take s Hs,
    show r_le s (reg_seq.mk t Ht), from
      have H' : ∀ n : ℕ+, r_le s (r_const (t n)), from Hs,
      by apply r_le_of_le_reprs; apply Hs)

theorem le_of_reprs_le (x : ℝ) (t : seq) (Ht : regular t) : (∀ n : ℕ+, t n ≤ x) →
        x ≥ ((quot.mk (reg_seq.mk t Ht)) : ℝ) :=
  quot.induction_on x (take s Hs,
    show r_le (reg_seq.mk t Ht) s, from
      have H' : ∀ n : ℕ+, r_le (r_const (t n)) s, from Hs,
      by apply r_le_of_reprs_le; apply Hs)

end real
