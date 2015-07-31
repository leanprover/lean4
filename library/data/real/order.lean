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
open -[coercions] rat
open -[coercions] nat
open eq eq.ops pnat
local notation 0 := rat.of_num 0
local notation 1 := rat.of_num 1
notation 2 := subtype.tag (of_num 2) dec_trivial

----------------------------------------------------------------------------------------------------

-- this could be moved to pnat, but it uses find_midpoint which still has sorries in real.basic
theorem sep_by_inv {a b : ℚ} (H : a > b) : ∃ N : ℕ+, a > (b + N⁻¹ + N⁻¹) :=
  begin
    apply exists.elim (find_midpoint H),
    intro c Hc,
    existsi (pceil ((1 + 1 + 1) / c)),
    apply rat.lt.trans,
    rotate 1,
    apply and.left Hc,
    rewrite rat.add.assoc,
    apply rat.add_lt_add_left,
    rewrite -(@rat.add_halves c) at {3},
    apply rat.add_lt_add,
    repeat (apply lt_of_le_of_lt;
    apply inv_pceil_div;
    apply dec_trivial;
    apply and.right Hc;
    apply div_lt_div_of_pos_of_lt_of_pos;
    repeat (apply dec_trivial);
    apply and.right Hc)
  end

theorem helper_1 {a : ℚ} (H : a > 0) : -a + -a ≤ -a :=
  !neg_add ▸ neg_le_neg (le_add_of_nonneg_left (le_of_lt H))

theorem rewrite_helper8 (a b c : ℚ) : a - b = c - b + (a - c) :=
  by rewrite[add_sub,rat.sub_add_cancel] ⬝ !rat.add.comm

theorem nonneg_of_ge_neg_invs (a : ℚ) (H : ∀ n : ℕ+, -n⁻¹ ≤ a) : 0 ≤ a :=
  rat.le_of_not_gt (suppose a < 0,
    have H2 : 0 < -a, from neg_pos_of_neg this,
   (rat.not_lt_of_ge !H) (iff.mp !lt_neg_iff_lt_neg (calc
       (pceil (of_num 2 / -a))⁻¹ ≤ -a / of_num 2
          : !inv_pceil_div dec_trivial H2
                             ... < -a / 1
          : div_lt_div_of_pos_of_lt_of_pos dec_trivial dec_trivial H2
                             ... = -a : div_one)))

---------
namespace s
definition pos (s : seq) := ∃ n : ℕ+, n⁻¹ < (s n)

definition nonneg (s : seq) := ∀ n : ℕ+, -(n⁻¹) ≤ s n

theorem bdd_away_of_pos {s : seq} (Hs : regular s) (H : pos s) :
        ∃ N : ℕ+, ∀ n : ℕ+, n ≥ N → (s n) ≥ N⁻¹ :=
  begin
    apply exists.elim H,
    intro n Hn,
    let Em := sep_by_inv Hn,
    apply exists.elim Em,
    intro N HN,
    existsi N,
    intro m Hm,
    have Habs : abs (s m - s n) ≥ s n - s m, by rewrite abs_sub; apply le_abs_self,
    have Habs' : s m + abs (s m - s n) ≥ s n, from (iff.mpr (le_add_iff_sub_left_le _ _ _)) Habs,
    have HN' : N⁻¹ + N⁻¹ ≤ s n - n⁻¹, begin
        apply iff.mpr (le_add_iff_sub_right_le _ _ _),
        rewrite [sub_neg_eq_add, add.comm, -add.assoc],
        apply le_of_lt HN
      end,
    rewrite rat.add.comm at Habs',
    have Hin : s m ≥ N⁻¹, from calc
      s m ≥ s n - abs (s m - s n) : (iff.mp (le_add_iff_sub_left_le _ _ _)) Habs'
      ... ≥ s n - (m⁻¹ + n⁻¹) : rat.sub_le_sub_left !Hs
      ... = s n - m⁻¹ - n⁻¹ : by rewrite sub_add_eq_sub_sub
      ... = s n - n⁻¹ - m⁻¹ : by rewrite [add.assoc, (add.comm (-m⁻¹)), -add.assoc]
      ... ≥ s n - n⁻¹ - N⁻¹ : rat.sub_le_sub_left (inv_ge_of_le Hm)
      ... ≥ N⁻¹ + N⁻¹ - N⁻¹ : rat.sub_le_sub_right HN'
      ... = N⁻¹ : by rewrite rat.add_sub_cancel,
    apply Hin
  end

theorem pos_of_bdd_away {s : seq} (H : ∃ N : ℕ+, ∀ n : ℕ+, n ≥ N → (s n) ≥ N⁻¹) : pos s :=
  begin
    rewrite ↑pos,
    apply exists.elim H,
    intro N HN,
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
    rewrite ↑nonneg at H,
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
    apply squeeze_2,
    intro ε Hε,
    apply exists.elim (H (pceil ((1 + 1) / ε))),
    intro N HN,
    let HN' := HN (max (pceil ((1+1)/ε)) N),
    let HN'' := HN' (!max_right),
    apply le.trans,
    rotate 1,
    apply ge_sub_of_abs_sub_le_left,
    apply Hs,
    apply (max (pceil ((1+1)/ε)) N),
    rewrite [↑rat.sub, neg_add, {_ + (-k⁻¹ + _)}add.comm, *add.assoc],
    apply rat.add_le_add_left,
    apply le.trans,
    rotate 1,
    apply rat.add_le_add,
    rotate 1,
    apply HN'',
    rotate_right 1,
    apply neg_le_neg,
    apply inv_ge_of_le,
    apply max_left,
    rewrite -neg_add,
    apply neg_le_neg,
    apply le.trans,
    apply rat.add_le_add,
    repeat (apply inv_pceil_div;
    apply rat.add_pos;
    repeat apply zero_lt_one;
    apply Hε),
    have Hone : 1 = of_num 1, from rfl,
    rewrite [Hone, add_halves],
    apply le.refl
  end

theorem pos_of_pos_equiv {s t : seq} (Hs : regular s) (Heq : s ≡ t) (Hp : pos s) : pos t :=
  begin
    rewrite [↑pos at *],
    apply exists.elim (bdd_away_of_pos Hs Hp),
    intro N HN,
    existsi 2 * 2 * N,
    apply lt_of_lt_of_le,
    rotate 1,
    apply ge_sub_of_abs_sub_le_right,
    apply Heq,
    have Hs4 : N⁻¹ ≤ s (2 * 2 * N), from HN _ (!mul_le_mul_left),
    apply lt_of_lt_of_le,
    rotate 1,
    apply iff.mpr (rat.add_le_add_right_iff _ _ _),
    apply Hs4,
    rewrite [*pnat.mul.assoc, pnat.add_halves, -(add_halves N), rat.add_sub_cancel],
    apply inv_two_mul_lt_inv
  end


theorem nonneg_of_nonneg_equiv {s t : seq} (Hs : regular s) (Ht : regular t) (Heq : s ≡ t)
        (Hp : nonneg s) : nonneg t :=
  begin
    apply nonneg_of_bdd_within,
    apply Ht,
    intros,
    let Bd := (bdd_within_of_nonneg Hs Hp) (2 * 2 * n),
    apply exists.elim Bd,
    intro Ns HNs,
    existsi max Ns (2 * 2 * n),
    intro m Hm,
    apply le.trans,
    rotate 1,
    apply ge_sub_of_abs_sub_le_right,
    apply Heq,
    apply le.trans,
    rotate 1,
    apply rat.sub_le_sub_right,
    apply HNs,
    apply pnat.le.trans,
    rotate 1,
    apply Hm,
    rotate_right 1,
    apply max_left,
    have Hms : m⁻¹ ≤ (2 * 2 * n)⁻¹, begin
         apply inv_ge_of_le,
         apply pnat.le.trans,
         rotate 1,
         apply Hm;
         apply max_right
      end,
    have Hms' : m⁻¹ + m⁻¹ ≤ (2 * 2 * n)⁻¹ + (2 * 2 * n)⁻¹, from add_le_add Hms Hms,
    apply le.trans,
    rotate 1,
    apply rat.sub_le_sub_left,
    apply Hms',
    rewrite [*pnat.mul.assoc, pnat.add_halves, -neg_add, -add_halves n],
    apply neg_le_neg,
    apply rat.add_le_add_right,
    apply inv_two_mul_le_inv
  end

definition s_le (a b : seq) := nonneg (sadd b (sneg a))
definition s_lt (a b : seq) := pos (sadd b (sneg a))

theorem zero_nonneg : nonneg zero :=
  begin
    rewrite ↑[nonneg, zero],
    intros,
    apply neg_nonpos_of_nonneg,
    apply le_of_lt,
    apply inv_pos
  end

theorem s_zero_lt_one : s_lt zero one :=
  begin
    rewrite [↑s_lt, ↑zero, ↑sadd, ↑sneg, ↑one, neg_zero, add_zero, ↑pos],
    existsi 2,
    apply inv_lt_one_of_gt,
    apply one_lt_two
  end

theorem le.refl {s : seq} (Hs : regular s) : s_le s s :=
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
    let Bt := bdd_away_of_pos Hs H,
    apply exists.elim Bt,
    intro N HN,
    existsi N,
    intro m Hm,
    apply le.trans,
    rotate 1,
    apply HN,
    apply Hm,
    apply le.trans,
    rotate 1,
    apply le_of_lt,
    apply inv_pos,
    rewrite -neg_zero,
    apply neg_le_neg,
    apply le_of_lt,
    apply inv_pos
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
    rewrite [rat.neg_add, sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem equiv_cancel_middle {s t u : seq} (Hs : regular s) (Ht : regular t)
        (Hu : regular u) : sadd (sadd u t) (sneg (sadd u s)) ≡ sadd t (sneg s) :=
  begin
    let Hz := zero_is_reg,
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

theorem add_le_add_of_le_right {s t : seq} (Hs : regular s) (Ht : regular t) (Lst : s_le s t) :
        ∀ u : seq, regular u → s_le (sadd u s) (sadd u t) :=
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

theorem add_nonneg_of_nonneg {s t : seq} (Hs : nonneg s) (Ht : nonneg t) : nonneg (sadd s t) :=
  begin
    rewrite [↑nonneg at *, ↑sadd],
    intros,
    rewrite [-pnat.add_halves, neg_add],
    apply add_le_add,
    apply Hs,
    apply Ht
  end

theorem le.trans {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u) (Lst : s_le s t)
        (Ltu : s_le t u) : s_le s u :=
  begin
    rewrite ↑s_le at *,
    let Rz := zero_is_reg,
    have Hsum : nonneg (sadd (sadd u (sneg t)) (sadd t (sneg s))),
                from add_nonneg_of_nonneg Ltu Lst,
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
    apply rat.le.trans,
    apply helper_1,
    apply inv_pos,
    rewrite add.comm,
    apply Lst,
    apply le_of_neg_le_neg,
    rewrite [neg_add, neg_neg],
    apply rat.le.trans,
    apply helper_1,
    apply inv_pos,
    apply Lts,
    repeat assumption
  end

definition sep (s t : seq) := s_lt s t ∨ s_lt t s
local infix `≢` : 50 := sep

theorem le_and_sep_of_lt {s t : seq} (Hs : regular s) (Ht : regular t) (Lst : s_lt s t) :
        s_le s t ∧ sep s t :=
  begin
    apply and.intro,
    rewrite [↑s_lt at *, ↑pos at *, ↑s_le, ↑nonneg],
    intros,
    apply exists.elim Lst,
    intro N HN,
    let Rns := reg_neg_reg Hs,
    let Rtns := reg_add_reg Ht Rns,
    let Habs := ge_sub_of_abs_sub_le_right (Rtns N n),
    rewrite [sub_add_eq_sub_sub at Habs],
    exact (calc
      sadd t (sneg s) n ≥ sadd t (sneg s) N -  N⁻¹ - n⁻¹ : Habs
      ... ≥ 0 - n⁻¹: begin
                       apply rat.sub_le_sub_right,
                       apply le_of_lt,
                       apply (iff.mpr (sub_pos_iff_lt _ _)),
                       apply HN
                     end
      ... = -n⁻¹ : by rewrite zero_sub),
    rewrite ↑sep,
    exact or.inl Lst
  end

theorem lt_of_le_and_sep {s t : seq} (Hs : regular s) (Ht : regular t) (H : s_le s t ∧ sep s t) :
        s_lt s t :=
  begin
    let Le := and.left H,
    let Hsep := and.right H,
    rewrite [↑sep at Hsep],
    apply or.elim Hsep,
    intro P, exact P,
    intro Hlt,
    rewrite [↑s_le at Le, ↑nonneg at Le, ↑s_lt at Hlt, ↑pos at Hlt],
    apply exists.elim Hlt,
    intro N HN,
    let LeN := Le N,
    let HN' := (iff.mpr (neg_lt_neg_iff_lt _ _)) HN,
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
    apply exists.elim (bdd_away_of_pos Hs Hps),
    intros Ns HNs,
    apply exists.elim (bdd_away_of_pos Ht Hpt),
    intros Nt HNt,
    existsi 2 * max Ns Nt * max Ns Nt,
    rewrite ↑smul,
    apply lt_of_lt_of_le,
    rotate 1,
    apply rat.mul_le_mul,
    apply HNs,
    apply pnat.le.trans,
    apply max_left Ns Nt,
    rewrite -pnat.mul.assoc,
    apply pnat.mul_le_mul_left,
    apply HNt,
    apply pnat.le.trans,
    apply max_right Ns Nt,
    rewrite -pnat.mul.assoc,
    apply pnat.mul_le_mul_left,
    apply le_of_lt,
    apply inv_pos,
    apply rat.le.trans,
    rotate 1,
    apply HNs,
    apply pnat.le.trans,
    apply max_left Ns Nt,
    rewrite -pnat.mul.assoc,
    apply pnat.mul_le_mul_left,
    rewrite inv_mul_eq_mul_inv,
    apply rat.mul_lt_mul,
    rewrite [inv_mul_eq_mul_inv, -one_mul Ns⁻¹],
    apply rat.mul_lt_mul,
    apply inv_lt_one_of_gt,
    apply dec_trivial,
    apply inv_ge_of_le,
    apply max_left,
    apply inv_pos,
    apply le_of_lt zero_lt_one,
    apply inv_ge_of_le,
    apply max_right,
    apply inv_pos,
    repeat (apply le_of_lt; apply inv_pos)
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
    apply rat.le.by_cases 0 (s (((K₂ s t) * 2) * n)),
    intro Hsp,
    apply rat.le.by_cases 0 (t (((K₂ s t) * 2) * n)),
    intro Htp,
    apply rat.le.trans,
    rotate 1,
    apply rat.mul_nonneg Hsp Htp,
    rotate_right 1,
    apply le_of_lt,
    apply neg_neg_of_pos,
    apply inv_pos,
      intro Htn,
      apply rat.le.trans,
      rotate 1,
      apply rat.mul_le_mul_of_nonpos_right,
      apply rat.le.trans,
      apply le_abs_self,
      apply canon_2_bound_left s t Hs,
      apply Htn,
      rotate_right 1,
      apply rat.le.trans,
      rotate 1,
      apply rat.mul_le_mul_of_nonneg_left,
      apply Hpt,
      apply le_of_lt,
      apply rat_of_pnat_is_pos,
      rotate 1,
      rewrite -neg_mul_eq_mul_neg,
      apply neg_le_neg,
      rewrite [*pnat.mul.assoc, inv_mul_eq_mul_inv, -mul.assoc, inv_cancel_left, one_mul],
      apply inv_ge_of_le,
      apply pnat.mul_le_mul_left,
     intro Hsn,
     apply rat.le.by_cases 0 (t (((K₂ s t) * 2) * n)),
     intro Htp,
     apply rat.le.trans,
     rotate 1,
     apply rat.mul_le_mul_of_nonpos_left,
     apply rat.le.trans,
     apply le_abs_self,
     apply canon_2_bound_right s t Ht,
     apply Hsn,
     rotate_right 1,
     apply rat.le.trans,
     rotate 1,
     apply rat.mul_le_mul_of_nonneg_right,
     apply Hps,
     apply le_of_lt,
     apply rat_of_pnat_is_pos,
     rotate 1,
     rewrite -neg_mul_eq_neg_mul,
     apply neg_le_neg,
     rewrite [*pnat.mul.assoc, inv_mul_eq_mul_inv, mul.comm, -mul.assoc, inv_cancel_left, one_mul],
     apply inv_ge_of_le,
     apply pnat.mul_le_mul_left,
    intro Htn,
    apply rat.le.trans,
    rotate 1,
    apply mul_nonneg_of_nonpos_of_nonpos,
    apply Hsn,
    apply Htn,
    apply le_of_lt,
    apply neg_neg_of_pos,
    apply inv_pos
  end

theorem s_mul_ge_zero_of_ge_zero {s t : seq} (Hs : regular s) (Ht : regular t)
        (Hzs : s_le zero s) (Hzt : s_le zero t) : s_le zero (smul s t) :=
  begin
    let Hzs' := s_nonneg_of_ge_zero Hs Hzs,
    let Htz' := s_nonneg_of_ge_zero Ht Hzt,
    apply s_ge_zero_of_nonneg,
    rotate 1,
    apply s_mul_nonneg_of_nonneg,
    repeat assumption,
    apply reg_mul_reg Hs Ht
  end



theorem not_lt_self (s : seq) : ¬ s_lt s s :=
  begin
    intro Hlt,
    rewrite [↑s_lt at Hlt, ↑pos at Hlt],
    apply exists.elim Hlt,
    intro n Hn, esimp at Hn,
    rewrite [↑sadd at Hn,↑sneg at Hn, sub_self at Hn],
    apply absurd Hn (rat.not_lt_of_ge (rat.le_of_lt !inv_pos))
  end


theorem not_sep_self (s : seq) : ¬ s ≢ s :=
  begin
    intro Hsep,
    rewrite ↑sep at Hsep,
    let Hsep' := (iff.mp (!or_self)) Hsep,
    apply absurd Hsep' (!not_lt_self)
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
      rewrite [↑sadd, ↑sneg, -rewrite_helper8]
    end,
    rewrite [↑s_lt at *, ↑s_le at *],
    apply exists.elim (bdd_away_of_pos Rtns Hst),
    intro Nt HNt,
    apply exists.elim (bdd_within_of_nonneg Runt Htu (2 * Nt)),
    intro Nu HNu,
    apply pos_of_bdd_away,
    existsi max (2 * Nt) Nu,
    intro n Hn,
    rewrite Hcan,
    apply rat.le.trans,
    rotate 1,
    apply rat.add_le_add,
    apply HNt,
    apply pnat.le.trans,
    apply mul_le_mul_left 2,
    apply pnat.le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply max_left,
    apply HNu,
    apply pnat.le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply max_right,
    rewrite [-add_halves Nt, rat.add_sub_cancel],
    apply inv_ge_of_le,
    apply max_left
  end

theorem s_lt_of_le_of_lt {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Hst : s_le s t) (Htu : s_lt t u) : s_lt s u :=
  begin
    let Rtns := reg_add_reg Ht (reg_neg_reg Hs),
    let Runt := reg_add_reg Hu (reg_neg_reg Ht),
    have Hcan : ∀ m, sadd u (sneg s) m = (sadd t (sneg s)) m + (sadd u (sneg t)) m, begin
      intro m,
      rewrite [↑sadd, ↑sneg, -rewrite_helper8]
    end,
    rewrite [↑s_lt at *, ↑s_le at *],
    apply exists.elim (bdd_away_of_pos Runt Htu),
    intro Nu HNu,
    apply exists.elim (bdd_within_of_nonneg Rtns Hst (2 * Nu)),
    intro Nt HNt,
    apply pos_of_bdd_away,
    existsi max (2 * Nu) Nt,
    intro n Hn,
    rewrite Hcan,
    apply rat.le.trans,
    rotate 1,
    apply rat.add_le_add,
    apply HNt,
    apply pnat.le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply max_right,
    apply HNu,
    apply pnat.le.trans,
    apply mul_le_mul_left 2,
    apply pnat.le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply max_left,
    rewrite [-add_halves Nu, neg_add_cancel_left],
    apply inv_ge_of_le,
    apply max_left
  end

theorem le_of_le_reprs {s t : seq} (Hs : regular s) (Ht : regular t)
        (Hle : ∀ n : ℕ+, s_le s (const (t n))) : s_le s t :=
  begin
    rewrite [↑s_le, ↑nonneg],
    intro m,
    apply Hle (2 * m) m
  end

theorem le_of_reprs_le {s t : seq} (Hs : regular s) (Ht : regular t)
        (Hle : ∀ n : ℕ+, s_le (const (t n)) s) : s_le t s :=
  begin
    rewrite [↑s_le, ↑nonneg],
    intro m,
    apply Hle (2 * m) m
  end

-----------------------------
-- of_rat theorems

theorem const_le_const_of_le {a b : ℚ} (H : a ≤ b) : s_le (const a) (const b) :=
  begin
    rewrite [↑s_le, ↑nonneg],
    intro n,
    rewrite [↑sadd, ↑sneg, ↑const],
    apply rat.le.trans,
    apply rat.neg_nonpos_of_nonneg,
    apply rat.le_of_lt,
    apply inv_pos,
    apply iff.mpr !rat.sub_nonneg_iff_le,
    apply H
  end

theorem le_of_const_le_const {a b : ℚ} (H : s_le (const a) (const b)) : a ≤ b :=
  begin
    rewrite [↑s_le at H, ↑nonneg at H, ↑sadd at H, ↑sneg at H, ↑const at H],
    apply iff.mp !rat.sub_nonneg_iff_le,
    apply nonneg_of_ge_neg_invs _ H
  end

theorem nat_inv_lt_rat {a : ℚ} (H : a > 0) : ∃ n : ℕ+, n⁻¹ < a :=
  begin
    existsi (pceil (1 / (a / (1 + 1)))),
    apply lt_of_le_of_lt,
    rotate 1,
    apply div_two_lt_of_pos H,
    rewrite -(@div_div' (a / (1 + 1))),
    apply pceil_helper,
    rewrite div_div',
    apply pnat.le.refl,
    apply div_pos_of_pos,
    apply pos_div_of_pos_of_pos H dec_trivial
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
    assumption,
    apply pnat.inv_pos
  end

theorem s_le_of_le_pointwise {s t : seq} (Hs : regular s) (Ht : s.regular t)
        (H : ∀ n : ℕ+, s n ≤ t n) : s_le s t :=
  begin
    rewrite [↑s_le, ↑nonneg, ↑sadd, ↑sneg],
    intros,
    apply rat.le.trans,
    apply iff.mpr !neg_nonpos_iff_nonneg,
    apply le_of_lt,
    apply inv_pos,
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

theorem r_le.refl (s : reg_seq) : r_le s s := le.refl (reg_seq.is_reg s)

theorem r_le.trans {s t u : reg_seq} (Hst : r_le s t) (Htu : r_le t u) : r_le s u :=
  le.trans (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u) Hst Htu

theorem r_equiv_of_le_of_ge {s t : reg_seq} (Hs : r_le s t) (Hu : r_le t s) :
        requiv s t :=
  equiv_of_le_of_ge (reg_seq.is_reg s) (reg_seq.is_reg t) Hs Hu

theorem r_lt_iff_le_and_sep (s t : reg_seq) : r_lt s t ↔ r_le s t ∧ r_sep s t :=
  lt_iff_le_and_sep (reg_seq.is_reg s) (reg_seq.is_reg t)

theorem r_add_le_add_of_le_right {s t : reg_seq} (H : r_le s t) (u : reg_seq) :
        r_le (u + s) (u + t) :=
  add_le_add_of_le_right (reg_seq.is_reg s) (reg_seq.is_reg t) H
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
  not_lt_self (reg_seq.sq s)

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

theorem r_le_of_reprs_le (s t : reg_seq) (Hle : ∀ n : ℕ+, r_le (r_const (reg_seq.sq t n)) s) : r_le t s :=
  le_of_reprs_le (reg_seq.is_reg s) (reg_seq.is_reg t) Hle

end s

open real
open [classes] s
namespace real

definition lt (x y : ℝ) := quot.lift_on₂ x y (λ a b, s.r_lt a b) s.r_lt_well_defined
infix [priority real.prio] `<` := lt

definition le (x y : ℝ) := quot.lift_on₂ x y (λ a b, s.r_le a b) s.r_le_well_defined
infix [priority real.prio] `≤` := le
infix [priority real.prio] `<=` := le

definition gt [reducible] (a b : ℝ) := lt b a
definition ge [reducible] (a b : ℝ) := le b a

infix [priority real.prio] >= := real.ge
infix [priority real.prio] ≥  := real.ge
infix [priority real.prio] >  := real.gt

definition sep (x y : ℝ) := quot.lift_on₂ x y (λ a b, s.r_sep a b) s.r_sep_well_defined
infix `≢` : 50 := sep

theorem le.refl (x : ℝ) : x ≤ x :=
  quot.induction_on x (λ t, s.r_le.refl t)

theorem le.trans (x y z : ℝ) : x ≤ y → y ≤ z → x ≤ z :=
  quot.induction_on₃ x y z (λ s t u, s.r_le.trans)

theorem eq_of_le_of_ge (x y : ℝ) : x ≤ y → y ≤ x → x = y :=
  quot.induction_on₂ x y (λ s t Hst Hts, quot.sound (s.r_equiv_of_le_of_ge Hst Hts))

theorem lt_iff_le_and_sep (x y : ℝ) : x < y ↔ x ≤ y ∧ x ≢ y :=
  quot.induction_on₂ x y (λ s t, s.r_lt_iff_le_and_sep s t)

theorem add_le_add_of_le_right_var (x y z : ℝ) : x ≤ y → z + x ≤ z + y :=
  quot.induction_on₃ x y z (λ s t u, s.r_add_le_add_of_le_right_var s t u)

theorem add_le_add_of_le_right (x y : ℝ) : x ≤ y → ∀ z : ℝ, z + x ≤ z + y :=
  take H z, add_le_add_of_le_right_var x y z H

theorem mul_gt_zero_of_gt_zero (x y : ℝ) : zero < x → zero < y → zero < x * y :=
  quot.induction_on₂ x y (λ s t, s.r_mul_pos_of_pos)

theorem mul_ge_zero_of_ge_zero (x y : ℝ) : zero ≤ x → zero ≤ y → zero ≤ x * y :=
  quot.induction_on₂ x y (λ s t, s.r_mul_nonneg_of_nonneg)

theorem not_sep_self (x : ℝ) : ¬ x ≢ x :=
  quot.induction_on x (λ s, s.r_not_sep_self s)

theorem not_lt_self (x : ℝ) : ¬ x < x :=
  quot.induction_on x (λ s, s.r_not_lt_self s)

theorem le_of_lt {x y : ℝ} : x < y → x ≤ y :=
  quot.induction_on₂ x y (λ s t H', s.r_le_of_lt H')

theorem lt_of_le_of_lt {x y z : ℝ} : x ≤ y → y < z → x < z :=
  quot.induction_on₃ x y z (λ s t u H H', s.r_lt_of_le_of_lt H H')

theorem lt_of_lt_of_le {x y z : ℝ} : x < y → y ≤ z → x < z :=
  quot.induction_on₃ x y z (λ s t u H H', s.r_lt_of_lt_of_le H H')

theorem add_lt_add_left_var (x y z : ℝ) : x < y → z + x < z + y :=
  quot.induction_on₃ x y z (λ s t u, s.r_add_lt_add_left_var s t u)

theorem add_lt_add_left (x y : ℝ) : x < y → ∀ z : ℝ, z + x < z + y :=
  take H z, add_lt_add_left_var x y z H

theorem zero_lt_one : zero < one := s.r_zero_lt_one

theorem le_of_lt_or_eq (x y : ℝ) : x < y ∨ x = y → x ≤ y :=
    (quot.induction_on₂ x y (λ s t H, or.elim H (take H', begin
        apply s.r_le_of_lt_or_eq,
        apply or.inl H'
      end)
      (take H', begin
        apply s.r_le_of_lt_or_eq,
        apply (or.inr (quot.exact H'))
      end)))

section migrate_algebra
  open [classes] algebra

  protected definition ordered_ring [reducible]  : algebra.ordered_ring ℝ :=
  ⦃ algebra.ordered_ring, real.comm_ring,
    le_refl := le.refl,
    le_trans := le.trans,
    mul_pos := mul_gt_zero_of_gt_zero,
    mul_nonneg := mul_ge_zero_of_ge_zero,
    zero_ne_one := zero_ne_one,
    add_le_add_left := add_le_add_of_le_right,
    le_antisymm := eq_of_le_of_ge,
    lt_irrefl := not_lt_self,
    lt_of_le_of_lt := @lt_of_le_of_lt,
    lt_of_lt_of_le := @lt_of_lt_of_le,
    le_of_lt := @le_of_lt,
    add_lt_add_left := add_lt_add_left
  ⦄

  local attribute real.comm_ring [instance]
  local attribute real.ordered_ring [instance]

  definition sub (a b : ℝ) : ℝ := algebra.sub a b
  infix [priority real.prio] - := real.sub
  definition dvd (a b : ℝ) : Prop := algebra.dvd a b
  notation [priority real.prio] a ∣ b := real.dvd a b

  migrate from algebra with real
    replacing has_le.ge → ge, has_lt.gt → gt, sub → sub, dvd → dvd, divide → divide

  attribute le.trans lt.trans lt_of_lt_of_le lt_of_le_of_lt ge.trans gt.trans gt_of_gt_of_ge
                   gt_of_ge_of_gt [trans]
end migrate_algebra

theorem of_rat_le_of_rat_of_le (a b : ℚ) : a ≤ b → of_rat a ≤ of_rat b :=
  s.r_const_le_const_of_le

theorem le_of_rat_le_of_rat (a b : ℚ) : of_rat a ≤ of_rat b → a ≤ b :=
  s.r_le_of_const_le_const

theorem of_rat_lt_of_rat_of_lt (a b : ℚ) : a < b → of_rat a < of_rat b :=
  s.r_const_lt_const_of_lt

theorem lt_of_rat_lt_of_rat (a b : ℚ) : of_rat a < of_rat b → a < b :=
  s.r_lt_of_const_lt_const

theorem of_rat_sub (a b : ℚ) : of_rat a - of_rat b = of_rat (a - b) := rfl

open s
theorem le_of_le_reprs (x : ℝ) (t : seq) (Ht : regular t) : (∀ n : ℕ+, x ≤ t n) →
        x ≤ quot.mk (reg_seq.mk t Ht) :=
  quot.induction_on x (take s Hs,
    show s.r_le s (reg_seq.mk t Ht), from
      have H' : ∀ n : ℕ+, r_le s (r_const (t n)), from Hs,
      by apply r_le_of_le_reprs; apply Hs)


theorem le_of_reprs_le (x : ℝ) (t : seq) (Ht : regular t) : (∀ n : ℕ+, t n ≤ x) →
        quot.mk (reg_seq.mk t Ht) ≤ x :=
  quot.induction_on x (take s Hs,
    show s.r_le (reg_seq.mk t Ht) s, from
      have H' : ∀ n : ℕ+, r_le (r_const (t n)) s, from Hs,
      by apply r_le_of_reprs_le; apply Hs)

end real
