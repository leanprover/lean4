/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
The real numbers, constructed as equivalence classes of Cauchy sequences of rationals.
This construction follows Bishop and Bridges (1985).

At this point, we no longer proceed constructively: this file makes heavy use of decidability
and excluded middle.
-/
import data.real.basic data.real.order data.rat data.nat
open rat
open nat
open eq.ops pnat classical algebra

namespace rat_seq
local postfix ⁻¹ := pnat.inv

-----------------------------
-- Facts about absolute values of sequences, to define inverse

definition s_abs (s : seq) : seq := λ n, abs (s n)

theorem abs_reg_of_reg {s : seq} (Hs : regular s) : regular (s_abs s) :=
  begin
    intros,
    apply algebra.le.trans,
    apply algebra.abs_abs_sub_abs_le_abs_sub,
    apply Hs
  end

theorem abs_pos_of_nonzero {s : seq} (Hs : regular s) (Hnz : sep s zero) :
        ∃ N : ℕ+, ∀ m : ℕ+, m ≥ N → abs (s m) ≥ N⁻¹ :=
  begin
    rewrite [↑sep at Hnz, ↑s_lt at Hnz],
    apply or.elim Hnz,
    intro Hnz1,
    have H' : pos (sneg s), begin
      apply pos_of_pos_equiv,
      rotate 2,
      apply Hnz1,
      rotate 1,
      apply s_zero_add,
      repeat (assumption | apply reg_add_reg | apply reg_neg_reg | apply zero_is_reg)
    end,
    cases bdd_away_of_pos (reg_neg_reg Hs) H' with [N, HN],
    existsi N,
    intro m Hm,
    apply rat.le.trans,
    apply HN m Hm,
    rewrite ↑sneg,
    apply neg_le_abs_self,
    intro Hnz2,
    let H' := pos_of_pos_equiv (reg_add_reg Hs (reg_neg_reg zero_is_reg)) (s_add_zero s Hs) Hnz2,
    let H'' := bdd_away_of_pos Hs H',
    cases H'' with [N, HN],
    existsi N,
    intro m Hm,
    apply rat.le.trans,
    apply HN m Hm,
    apply le_abs_self
  end

theorem abs_well_defined {s t : seq} (Hs : regular s) (Ht : regular t) (Heq : s ≡ t) :
        s_abs s ≡ s_abs t :=
  begin
    rewrite [↑equiv at *],
    intro n,
    rewrite ↑s_abs,
    apply rat.le.trans,
    apply abs_abs_sub_abs_le_abs_sub,
    apply Heq
  end

theorem sep_zero_of_pos {s : seq} (Hs : regular s) (Hpos : pos s) : sep s zero :=
  begin
    apply or.inr,
    apply pos_of_pos_equiv,
    rotate 2,
    apply Hpos,
    apply Hs,
    apply equiv.symm,
    apply s_sub_zero Hs
  end

------------------------
-- This section could be cleaned up.

private noncomputable definition pb {s : seq} (Hs : regular s) (Hpos : pos s) :=
  some (abs_pos_of_nonzero Hs (sep_zero_of_pos Hs Hpos))
private noncomputable definition ps {s : seq} (Hs : regular s) (Hsep : sep s zero) :=
  some (abs_pos_of_nonzero Hs Hsep)


private theorem pb_spec {s : seq} (Hs : regular s) (Hpos : pos s) :
        ∀ m : ℕ+, m ≥ (pb Hs Hpos) → abs (s m) ≥ (pb Hs Hpos)⁻¹ :=
  some_spec (abs_pos_of_nonzero Hs (sep_zero_of_pos Hs Hpos))

private theorem ps_spec {s : seq} (Hs : regular s) (Hsep : sep s zero) :
        ∀ m : ℕ+, m ≥ (ps Hs Hsep) → abs (s m) ≥ (ps Hs Hsep)⁻¹ :=
  some_spec (abs_pos_of_nonzero Hs Hsep)

noncomputable definition s_inv {s : seq} (Hs : regular s) (n : ℕ+) : ℚ :=
  if H : sep s zero then
      (if n < (ps Hs H) then 1 / (s ((ps Hs H) * (ps Hs H) * (ps Hs H)))
        else 1 / (s ((ps Hs H) * (ps Hs H) * n)))
  else 0

private theorem peq {s : seq} (Hsep : sep s zero) (Hpos : pos s)  (Hs : regular s) :
        pb Hs Hpos = ps Hs Hsep := rfl

private theorem s_inv_of_sep_lt_p {s : seq} (Hs : regular s) (Hsep : sep s zero) {n : ℕ+}
        (Hn : n < (ps Hs Hsep)) : s_inv Hs n = 1 / s ((ps Hs Hsep) * (ps Hs Hsep) * (ps Hs Hsep)) :=
  begin
    apply eq.trans,
    apply dif_pos Hsep,
    apply dif_pos Hn
  end

private theorem s_inv_of_sep_gt_p {s : seq} (Hs : regular s) (Hsep : sep s zero) {n : ℕ+}
        (Hn : n ≥ (ps Hs Hsep)) : s_inv Hs n = 1 / s ((ps Hs Hsep) * (ps Hs Hsep) * n) :=
  begin
    apply eq.trans,
    apply dif_pos Hsep,
    apply dif_neg (pnat.not_lt_of_ge Hn)
  end

private theorem s_inv_of_pos_lt_p {s : seq} (Hs : regular s) (Hpos : pos s) {n : ℕ+}
        (Hn : n < (pb Hs Hpos)) : s_inv Hs n = 1 / s ((pb Hs Hpos) * (pb Hs Hpos) * (pb Hs Hpos)) :=
  s_inv_of_sep_lt_p Hs (sep_zero_of_pos Hs Hpos) Hn

private theorem s_inv_of_pos_gt_p {s : seq} (Hs : regular s) (Hpos : pos s) {n : ℕ+}
        (Hn : n ≥ (pb Hs Hpos)) : s_inv Hs n = 1 / s ((pb Hs Hpos) * (pb Hs Hpos) * n) :=
  s_inv_of_sep_gt_p Hs (sep_zero_of_pos Hs Hpos) Hn

private theorem le_ps {s : seq} (Hs : regular s) (Hsep : sep s zero) (n : ℕ+) :
        abs (s_inv Hs n) ≤ (rat_of_pnat (ps Hs Hsep)) :=
  if Hn : n < ps Hs Hsep then
    (begin
      rewrite [(s_inv_of_sep_lt_p Hs Hsep Hn), abs_one_div],
      apply div_le_pnat,
      apply ps_spec,
      apply pnat.mul_le_mul_left
    end)
  else
    (begin
      rewrite [(s_inv_of_sep_gt_p Hs Hsep (le_of_not_gt Hn)), abs_one_div],
      apply div_le_pnat,
      apply ps_spec,
      rewrite pnat.mul.assoc,
      apply pnat.mul_le_mul_right
    end)

theorem s_inv_zero : s_inv zero_is_reg = zero :=
  funext (λ n, dif_neg (!not_sep_self))

private theorem s_inv_of_zero' {s : seq} (Hs : regular s) (Hz : ¬ sep s zero) (n : ℕ+) : s_inv Hs n = 0 :=
  dif_neg Hz

theorem s_inv_of_zero {s : seq} (Hs : regular s) (Hz : ¬ sep s zero) : s_inv Hs = zero :=
  begin
    apply funext,
    intro n,
    apply s_inv_of_zero' Hs Hz n
  end

private theorem s_ne_zero_of_ge_p {s : seq} (Hs : regular s) (Hsep : sep s zero) {n : ℕ+}
        (Hn : n ≥ (ps Hs Hsep)) : s n ≠ 0 :=
  begin
    let Hps := ps_spec Hs Hsep,
    apply ne_zero_of_abs_ne_zero,
    apply ne_of_gt,
    apply gt_of_ge_of_gt,
    apply Hps,
    apply Hn,
    apply inv_pos
  end

theorem reg_inv_reg {s : seq} (Hs : regular s) (Hsep : sep s zero) : regular (s_inv Hs) :=
  begin
    rewrite ↑regular,
    intros,
    have Hsp : s ((ps Hs Hsep) * (ps Hs Hsep) * (ps Hs Hsep)) ≠ 0, from
      s_ne_zero_of_ge_p Hs Hsep !mul_le_mul_left,
    have Hspn : s ((ps Hs Hsep) * (ps Hs Hsep) * n) ≠ 0, from
      s_ne_zero_of_ge_p Hs Hsep (show (ps Hs Hsep) * (ps Hs Hsep) * n ≥ ps Hs Hsep, by
        rewrite pnat.mul.assoc; apply pnat.mul_le_mul_right),
    have Hspm : s ((ps Hs Hsep) * (ps Hs Hsep) * m) ≠ 0, from
      s_ne_zero_of_ge_p Hs Hsep (show (ps Hs Hsep) * (ps Hs Hsep) * m ≥ ps Hs Hsep, by
        rewrite pnat.mul.assoc; apply pnat.mul_le_mul_right),
    cases em (m < ps Hs Hsep) with [Hmlt, Hmlt],
      cases em (n < ps Hs Hsep) with [Hnlt, Hnlt],
        rewrite [(s_inv_of_sep_lt_p Hs Hsep Hmlt), (s_inv_of_sep_lt_p Hs Hsep Hnlt)],
        rewrite [algebra.sub_self, abs_zero],
        apply add_invs_nonneg,
       rewrite [(s_inv_of_sep_lt_p Hs Hsep Hmlt),
                (s_inv_of_sep_gt_p Hs Hsep (le_of_not_gt Hnlt))],
       rewrite [(!div_sub_div Hsp Hspn), div_eq_mul_one_div, *abs_mul, *mul_one, *one_mul],
       apply rat.le.trans,
       apply algebra.mul_le_mul,
       apply Hs,
       rewrite [-(mul_one 1), -(!field.div_mul_div Hsp Hspn), abs_mul],
       apply algebra.mul_le_mul,
       rewrite -(s_inv_of_sep_lt_p Hs Hsep Hmlt),
       apply le_ps Hs Hsep,
       rewrite  -(s_inv_of_sep_gt_p Hs Hsep (le_of_not_gt Hnlt)),
       apply le_ps Hs Hsep,
       apply abs_nonneg,
       apply le_of_lt !rat_of_pnat_is_pos,
       apply abs_nonneg,
       apply add_invs_nonneg,
       rewrite [right_distrib, *pnat_cancel', rat.add.comm],
       apply algebra.add_le_add_right,
       apply inv_ge_of_le,
       apply pnat.le_of_lt,
       apply Hmlt,
      cases em (n < ps Hs Hsep) with [Hnlt, Hnlt],
        rewrite [(s_inv_of_sep_lt_p Hs Hsep Hnlt),
                 (s_inv_of_sep_gt_p Hs Hsep (le_of_not_gt Hmlt))],
        rewrite [(!div_sub_div Hspm Hsp), div_eq_mul_one_div, *abs_mul, *mul_one, *one_mul],
        apply rat.le.trans,
        apply algebra.mul_le_mul,
        apply Hs,
        rewrite [-(mul_one 1), -(!field.div_mul_div Hspm Hsp), abs_mul],
        apply algebra.mul_le_mul,
        rewrite -(s_inv_of_sep_gt_p Hs Hsep (le_of_not_gt Hmlt)),
        apply le_ps Hs Hsep,
        rewrite -(s_inv_of_sep_lt_p Hs Hsep Hnlt),
        apply le_ps Hs Hsep,
        apply abs_nonneg,
        apply le_of_lt !rat_of_pnat_is_pos,
        apply abs_nonneg,
        apply add_invs_nonneg,
        rewrite [right_distrib, *pnat_cancel', rat.add.comm],
        apply rat.add_le_add_left,
        apply inv_ge_of_le,
        apply pnat.le_of_lt,
        apply Hnlt,
      rewrite [(s_inv_of_sep_gt_p Hs Hsep (le_of_not_gt Hnlt)),
              (s_inv_of_sep_gt_p Hs Hsep (le_of_not_gt Hmlt))],
      rewrite [(!div_sub_div Hspm Hspn), div_eq_mul_one_div, abs_mul, *one_mul, *mul_one],
      apply rat.le.trans,
      apply algebra.mul_le_mul,
      apply Hs,
      rewrite [-(mul_one 1), -(!field.div_mul_div Hspm Hspn), abs_mul],
      apply algebra.mul_le_mul,
      rewrite -(s_inv_of_sep_gt_p Hs Hsep (le_of_not_gt Hmlt)),
      apply le_ps Hs Hsep,
      rewrite -(s_inv_of_sep_gt_p Hs Hsep (le_of_not_gt Hnlt)),
      apply le_ps Hs Hsep,
      apply abs_nonneg,
      apply le_of_lt !rat_of_pnat_is_pos,
      apply abs_nonneg,
      apply add_invs_nonneg,
      rewrite [right_distrib, *pnat_cancel', rat.add.comm],
      apply rat.le.refl
  end

theorem s_inv_ne_zero {s : seq} (Hs : regular s) (Hsep : sep s zero) (n : ℕ+) : s_inv Hs n ≠ 0 :=
  if H : n ≥ ps Hs Hsep then
    (begin
      rewrite (s_inv_of_sep_gt_p Hs Hsep H),
      apply one_div_ne_zero,
      apply s_ne_zero_of_ge_p,
      apply pnat.le.trans,
      apply H,
      apply pnat.mul_le_mul_left
    end)
  else
    (begin
      rewrite (s_inv_of_sep_lt_p Hs Hsep (pnat.lt_of_not_le H)),
      apply one_div_ne_zero,
      apply s_ne_zero_of_ge_p,
      apply pnat.mul_le_mul_left
    end)

theorem mul_inv {s : seq} (Hs : regular s) (Hsep : sep s zero) : smul s (s_inv Hs) ≡ one :=
  begin
    let Rsi := reg_inv_reg Hs Hsep,
    let Rssi := reg_mul_reg Hs Rsi,
    apply eq_of_bdd Rssi one_is_reg,
    intros,
    existsi max (ps Hs Hsep) j,
    intro n Hn,
    have Hnz : s_inv Hs ((K₂ s (s_inv Hs)) * 2 * n) ≠ 0, from s_inv_ne_zero Hs Hsep _,
    rewrite [↑smul, ↑one, rat.mul.comm, -(mul_one_div_cancel Hnz),
            -algebra.mul_sub_left_distrib, abs_mul],
    apply rat.le.trans,
    apply mul_le_mul_of_nonneg_right,
    apply canon_2_bound_right s,
    apply Rsi,
    apply abs_nonneg,
    have Hp : (K₂ s (s_inv Hs)) * 2 * n ≥ ps Hs Hsep, begin
      apply pnat.le.trans,
      apply max_left,
      rotate 1,
      apply pnat.le.trans,
      apply Hn,
      apply pnat.mul_le_mul_left
    end,
    have Hnz' : s (((ps Hs Hsep) * (ps Hs Hsep)) * ((K₂ s (s_inv Hs)) * 2 * n)) ≠ 0, from
      s_ne_zero_of_ge_p Hs Hsep
        (show ps Hs Hsep ≤ ((ps Hs Hsep) * (ps Hs Hsep)) * ((K₂ s (s_inv Hs)) * 2 * n),
          by rewrite *pnat.mul.assoc; apply pnat.mul_le_mul_right),
    rewrite [(s_inv_of_sep_gt_p Hs Hsep Hp), (division_ring.one_div_one_div Hnz')],
    apply rat.le.trans,
    apply mul_le_mul_of_nonneg_left,
    apply Hs,
    apply le_of_lt,
    apply rat_of_pnat_is_pos,
    rewrite [rat.mul.left_distrib, mul.comm ((ps Hs Hsep) * (ps Hs Hsep)), *pnat.mul.assoc,
            *(@inv_mul_eq_mul_inv (K₂ s (s_inv Hs))), -*rat.mul.assoc, *inv_cancel_left,
            *one_mul, -(add_halves j)],
    apply add_le_add,
    apply inv_ge_of_le,
    apply pnat_mul_le_mul_left',
    apply pnat.le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply max_right,
    apply inv_ge_of_le,
    apply pnat_mul_le_mul_left',
    apply pnat.le.trans,
    apply max_right,
    rotate 1,
    apply pnat.le.trans,
    apply Hn,
    apply pnat.mul_le_mul_right
   end

theorem inv_mul {s : seq} (Hs : regular s) (Hsep : sep s zero) : smul (s_inv Hs) s ≡ one :=
  begin
    apply equiv.trans,
    rotate 3,
    apply s_mul_comm,
    apply mul_inv,
    repeat (assumption | apply reg_mul_reg | apply reg_inv_reg | apply zero_is_reg)
  end

theorem sep_of_equiv_sep {s t : seq} (Hs : regular s) (Ht : regular t) (Heq : s ≡ t)
        (Hsep : sep s zero) : sep t zero :=
  begin
    apply or.elim Hsep,
    intro Hslt,
    apply or.inl,
    rewrite ↑s_lt at *,
    apply pos_of_pos_equiv,
    rotate 2,
    apply Hslt,
    rotate_right 1,
    apply add_well_defined,
    rotate 4,
    apply equiv.refl,
    apply neg_well_defined,
    apply Heq,
    intro Hslt,
    apply or.inr,
    rewrite ↑s_lt at *,
    apply pos_of_pos_equiv,
    rotate 2,
    apply Hslt,
    rotate_right 1,
    apply add_well_defined,
    rotate 5,
    apply equiv.refl,
    repeat (assumption | apply reg_neg_reg | apply reg_add_reg | apply zero_is_reg)
  end

theorem inv_unique {s t : seq} (Hs : regular s) (Ht : regular t) (Hsep : sep s zero)
        (Heq : smul s t ≡ one) : s_inv Hs ≡ t :=
  begin
    apply equiv.trans,
    rotate 3,
    apply equiv.symm,
    apply s_mul_one,
    rotate 1,
    apply equiv.trans,
    rotate 3,
    apply mul_well_defined,
    rotate 4,
    apply equiv.refl,
    apply equiv.symm,
    apply Heq,
    apply equiv.trans,
    rotate 3,
    apply equiv.symm,
    apply s_mul_assoc,
    rotate 3,
    apply equiv.trans,
    rotate 3,
    apply mul_well_defined,
    rotate 4,
    apply inv_mul,
    rotate 1,
    apply equiv.refl,
    apply s_one_mul,
    repeat (assumption | apply reg_inv_reg | apply reg_mul_reg | apply one_is_reg)
  end

theorem inv_well_defined {s t : seq} (Hs : regular s) (Ht : regular t) (Heq : s ≡ t) :
        s_inv Hs ≡ s_inv Ht :=
  if Hsep : sep s zero then
    (begin
       let Hsept := sep_of_equiv_sep Hs Ht Heq Hsep,
       have Hm : smul t (s_inv Hs) ≡ smul s (s_inv Hs), begin
         apply mul_well_defined,
         repeat (assumption | apply reg_inv_reg),
         apply equiv.symm s t Heq,
         apply equiv.refl
       end,
       apply equiv.symm,
       apply inv_unique,
       rotate 2,
       apply equiv.trans,
       rotate 3,
       apply Hm,
       apply mul_inv,
       repeat (assumption | apply reg_inv_reg | apply reg_mul_reg),
       apply one_is_reg
     end)
  else
    (assert H : s_inv Hs = zero, from funext (λ n, dif_neg Hsep),
     have Hsept : ¬ sep t zero, from
       assume H', Hsep (sep_of_equiv_sep Ht Hs (equiv.symm _ _ Heq) H'),
     assert H' : s_inv Ht = zero, from funext (λ n, dif_neg Hsept),
     by rewrite [H', H]; apply equiv.refl)

theorem s_neg_neg {s : seq} : sneg (sneg s) ≡ s :=
  begin
    rewrite [↑equiv, ↑sneg],
    intro n,
    rewrite [neg_neg, algebra.sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem s_neg_sub {s t : seq} (Hs : regular s) (Ht : regular t) :
        sneg (sadd s (sneg t)) ≡ sadd t (sneg s) :=
  begin
    apply equiv.trans,
    rotate 3,
    apply s_neg_add_eq_s_add_neg,
    apply equiv.trans,
    rotate 3,
    apply add_well_defined,
    rotate 4,
    apply equiv.refl,
    apply s_neg_neg,
    apply s_add_comm,
    repeat (assumption | apply reg_add_reg | apply reg_neg_reg)
  end

theorem s_le_total {s t : seq} (Hs : regular s) (Ht : regular t) : s_le s t ∨ s_le t s :=
  if H : s_le s t then or.inl H else or.inr begin
      rewrite [↑s_le at *],
      have H' : ∃ n : ℕ+, -n⁻¹ > sadd t (sneg s) n, begin
        apply by_contradiction,
        intro Hex,
        have Hex' : ∀ n : ℕ+, -n⁻¹ ≤ sadd t (sneg s) n, begin
          intro m,
          apply by_contradiction,
          intro Hm,
          let Hm' := lt_of_not_ge Hm,
          let Hex'' := exists.intro m Hm',
          apply Hex Hex''
        end,
        apply H Hex'
      end,
      eapply exists.elim H',
      intro m Hm,
      let Hm' := neg_lt_neg Hm,
      rewrite neg_neg at Hm',
      apply s_nonneg_of_pos,
      rotate 1,
      apply pos_of_pos_equiv,
      rotate 1,
      apply s_neg_sub,
      rotate 2,
      rewrite [↑pos, ↑sneg],
      existsi m,
      apply Hm',
      repeat (assumption | apply reg_add_reg | apply reg_neg_reg)
    end

theorem s_le_of_not_lt {s t : seq} (Hle : ¬ s_lt s t) : s_le t s :=
  begin
    rewrite [↑s_le, ↑nonneg, ↑s_lt at Hle, ↑pos at Hle],
    let Hle' := iff.mp forall_iff_not_exists Hle,
    intro n,
    let Hn := neg_le_neg (le_of_not_gt (Hle' n)),
    rewrite [↑sadd, ↑sneg, add_neg_eq_neg_add_rev],
    apply Hn
  end

theorem sep_of_nequiv {s t : seq} (Hs : regular s) (Ht : regular t) (Hneq : ¬ equiv s t) :
        sep s t :=
  begin
    rewrite ↑sep,
    apply by_contradiction,
    intro Hnor,
    let Hand := iff.mp !not_or_iff_not_and_not Hnor,
    let Hle1 := s_le_of_not_lt (and.left Hand),
    let Hle2 := s_le_of_not_lt (and.right Hand),
    apply Hneq (equiv_of_le_of_ge Hs Ht Hle2 Hle1)
  end

theorem s_zero_inv_equiv_zero : s_inv zero_is_reg ≡ zero :=
  by rewrite s_inv_zero; apply equiv.refl

theorem lt_or_equiv_of_le {s t : seq} (Hs : regular s) (Ht : regular t) (Hle : s_le s t) :
        s_lt s t ∨ s ≡ t :=
  if H : s ≡ t then or.inr H else
    or.inl (lt_of_le_and_sep Hs Ht (and.intro Hle (sep_of_nequiv Hs Ht H)))

theorem s_le_of_equiv_le_left {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Heq : s ≡ t) (Hle : s_le s u) : s_le t u :=
  begin
    rewrite ↑s_le at *,
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply add_well_defined,
    rotate 4,
    apply equiv.refl,
    apply neg_well_defined,
    apply Heq,
    repeat (assumption | apply reg_add_reg | apply reg_neg_reg)
  end

theorem s_le_of_equiv_le_right {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Heq : t ≡ u) (Hle : s_le s t) : s_le s u :=
  begin
    rewrite ↑s_le at *,
    apply nonneg_of_nonneg_equiv,
    rotate 2,
    apply add_well_defined,
    rotate 4,
    apply Heq,
    apply equiv.refl,
    repeat (assumption | apply reg_add_reg | apply reg_neg_reg)
  end

-----------------------------

noncomputable definition r_inv (s : reg_seq) : reg_seq := reg_seq.mk (s_inv (reg_seq.is_reg s))
  (if H : sep (reg_seq.sq s) zero then reg_inv_reg (reg_seq.is_reg s) H else
    assert Hz : s_inv (reg_seq.is_reg s) = zero, from funext (λ n, dif_neg H), by rewrite Hz; apply zero_is_reg)

theorem r_inv_zero : requiv (r_inv r_zero) r_zero :=
  s_zero_inv_equiv_zero


theorem r_inv_well_defined {s t : reg_seq} (H : requiv s t) : requiv (r_inv s) (r_inv t) :=
  inv_well_defined (reg_seq.is_reg s) (reg_seq.is_reg t) H

theorem r_le_total (s t : reg_seq) : r_le s t ∨ r_le t s :=
  s_le_total (reg_seq.is_reg s) (reg_seq.is_reg t)

theorem r_mul_inv (s : reg_seq) (Hsep : r_sep s r_zero) : requiv (s * (r_inv s)) r_one :=
  mul_inv (reg_seq.is_reg s) Hsep

theorem r_sep_of_nequiv (s t : reg_seq) (Hneq : ¬ requiv s t) : r_sep s t :=
  sep_of_nequiv (reg_seq.is_reg s) (reg_seq.is_reg t) Hneq

theorem r_lt_or_equiv_of_le (s t : reg_seq) (Hle : r_le s t) : r_lt s t ∨ requiv s t :=
  lt_or_equiv_of_le (reg_seq.is_reg s) (reg_seq.is_reg t) Hle

theorem r_le_of_equiv_le_left {s t u : reg_seq} (Heq : requiv s t) (Hle : r_le s u) : r_le t u :=
  s_le_of_equiv_le_left (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u) Heq Hle

theorem r_le_of_equiv_le_right {s t u : reg_seq} (Heq : requiv t u) (Hle : r_le s t) : r_le s u :=
  s_le_of_equiv_le_right (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u) Heq Hle

definition r_abs (s : reg_seq) : reg_seq :=
  reg_seq.mk (s_abs (reg_seq.sq s)) (abs_reg_of_reg (reg_seq.is_reg s))

theorem r_abs_well_defined {s t : reg_seq} (H : requiv s t) : requiv (r_abs s) (r_abs t) :=
  abs_well_defined (reg_seq.is_reg s) (reg_seq.is_reg t) H

end rat_seq

namespace real
open [classes] rat_seq

noncomputable protected definition inv (x : ℝ) : ℝ := quot.lift_on x (λ a, quot.mk (rat_seq.r_inv a))
           (λ a b H, quot.sound (rat_seq.r_inv_well_defined H))

noncomputable definition real_has_inv [instance] [reducible] [priority real.prio] : has_inv real :=
has_inv.mk real.inv

noncomputable protected definition division (x y : ℝ) : ℝ :=
x * y⁻¹

noncomputable definition real_has_division [instance] [reducible] [priority real.prio] : has_division real :=
has_division.mk real.division

theorem le_total (x y : ℝ) : x ≤ y ∨ y ≤ x :=
  quot.induction_on₂ x y (λ s t, rat_seq.r_le_total s t)

theorem mul_inv' (x : ℝ) : x ≢ 0 → x * x⁻¹ = 1 :=
  quot.induction_on x (λ s H, quot.sound (rat_seq.r_mul_inv s H))

theorem inv_mul' (x : ℝ) : x ≢ 0 → x⁻¹ * x = 1 :=
  by rewrite real.mul_comm; apply mul_inv'

theorem neq_of_sep {x y : ℝ} (H : x ≢ y) : ¬ x = y :=
  assume Heq, !not_sep_self (Heq ▸ H)

theorem sep_of_neq {x y : ℝ} : ¬ x = y → x ≢ y :=
  quot.induction_on₂ x y (λ s t H, rat_seq.r_sep_of_nequiv s t (assume Heq, H (quot.sound Heq)))

theorem sep_is_neq (x y : ℝ) : (x ≢ y) = (¬ x = y) :=
  propext (iff.intro neq_of_sep sep_of_neq)

theorem mul_inv (x : ℝ) : x ≠ 0 → x * x⁻¹ = 1 := !sep_is_neq ▸ !mul_inv'

theorem inv_mul (x : ℝ) : x ≠ 0 → x⁻¹ * x = 1 := !sep_is_neq ▸ !inv_mul'

theorem inv_zero : (0 : ℝ)⁻¹ = 0 := quot.sound (rat_seq.r_inv_zero)

theorem lt_or_eq_of_le (x y : ℝ) : x ≤ y → x < y ∨ x = y :=
  quot.induction_on₂ x y (λ s t H, or.elim (rat_seq.r_lt_or_equiv_of_le s t H)
    (assume H1, or.inl H1)
    (assume H2, or.inr (quot.sound H2)))

theorem le_iff_lt_or_eq (x y : ℝ) : x ≤ y ↔ x < y ∨ x = y :=
  iff.intro (lt_or_eq_of_le x y) (le_of_lt_or_eq x y)

noncomputable definition dec_lt : decidable_rel real.lt :=
  begin
    rewrite ↑decidable_rel,
    intros,
    apply prop_decidable
  end

protected noncomputable definition discrete_linear_ordered_field [reducible] [trans_instance]:
  algebra.discrete_linear_ordered_field ℝ :=
  ⦃ algebra.discrete_linear_ordered_field, real.comm_ring, real.ordered_ring,
    le_total := le_total,
    mul_inv_cancel := mul_inv,
    inv_mul_cancel := inv_mul,
    zero_lt_one := zero_lt_one,
    inv_zero := inv_zero,
    le_iff_lt_or_eq := le_iff_lt_or_eq,
    decidable_lt := dec_lt
   ⦄

theorem of_rat_zero : of_rat (0:rat) = (0:real) := rfl

theorem of_rat_one : of_rat (1:rat) = (1:real) := rfl

theorem of_rat_divide (x y : ℚ) : of_rat (x / y) = of_rat x / of_rat y :=
by_cases
  (assume yz : y = 0, by krewrite [yz, algebra.div_zero, +of_rat_zero, algebra.div_zero])
  (assume ynz : y ≠ 0,
    have ynz' : of_rat y ≠ 0, from assume yz', ynz (of_rat.inj yz'),
    !eq_div_of_mul_eq ynz' (by krewrite [-of_rat_mul, !div_mul_cancel ynz]))

open int

theorem of_int_div (x y : ℤ) (H : (#int y ∣ x)) : of_int ((x div y)) = of_int x / of_int y :=
by rewrite [of_int_eq, rat.of_int_div H, of_rat_divide]

theorem of_nat_div (x y : ℕ) (H : (#nat y ∣ x)) : of_nat (x div y) = of_nat x / of_nat y :=
by rewrite [of_nat_eq, rat.of_nat_div H, of_rat_divide]

/- useful for proving equalities -/

theorem eq_zero_of_nonneg_of_forall_lt {x : ℝ} (xnonneg : x ≥ 0) (H : ∀ ε : ℝ, ε > 0 → x < ε) :
  x = 0 :=
decidable.by_contradiction
  (suppose x ≠ 0,
   have x > 0, from lt_of_le_of_ne xnonneg (ne.symm this),
   have x < x, from H x this,
   show false, from !lt.irrefl this)

theorem eq_zero_of_nonneg_of_forall_le {x : ℝ} (xnonneg : x ≥ 0) (H : ∀ ε : ℝ, ε > 0 → x ≤ ε) :
  x = 0 :=
have ∀ ε : ℝ, ε > 0 → x < ε, from
  take ε, suppose ε > 0,
  assert e2pos : ε / 2 > 0, from div_pos_of_pos_of_pos `ε > 0` two_pos,
  assert ε / 2 < ε, from div_two_lt_of_pos `ε > 0`,
  begin apply algebra.lt_of_le_of_lt, apply H _ e2pos, apply this end,
eq_zero_of_nonneg_of_forall_lt xnonneg this

theorem eq_zero_of_forall_abs_le {x : ℝ} (H : ∀ ε : ℝ, ε > 0 → abs x ≤ ε) :
  x = 0 :=
by_contradiction
  (suppose x ≠ 0,
   have abs x = 0, from eq_zero_of_nonneg_of_forall_le !abs_nonneg H,
   show false, from `x ≠ 0` (eq_zero_of_abs_eq_zero this))

theorem eq_of_forall_abs_sub_le {x y : ℝ} (H : ∀ ε : ℝ, ε > 0 → abs (x - y) ≤ ε) :
  x = y :=
have x - y = 0, from eq_zero_of_forall_abs_le H,
eq_of_sub_eq_zero this
end real
