/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
The real numbers, constructed as equivalence classes of Cauchy sequences of rationals.
This construction follows Bishop and Bridges (1985).

At this point, we no longer proceed constructively: this file makes heavy use of decidability,
 excluded middle, and Hilbert choice.

Here, we show that ℝ is complete.
-/

import data.real.basic data.real.order data.real.division data.rat data.nat data.pnat
import logic.choice
open -[coercions] rat
local notation 0 := rat.of_num 0
local notation 1 := rat.of_num 1
open -[coercions] nat
open eq.ops
open pnat


local notation 2 := subtype.tag (nat.of_num 2) dec_trivial
local notation 3 := subtype.tag (nat.of_num 3) dec_trivial

namespace s


theorem rat_approx_l1 {s : seq} (H : regular s) :
        ∀ n : ℕ+, ∃ q : ℚ, ∃ N : ℕ+, ∀ m : ℕ+, m ≥ N → abs (s m - q) ≤ n⁻¹ :=
  begin
    intro n,
    existsi (s (2 * n)),
    existsi 2 * n,
    intro m Hm,
    apply rat.le.trans,
    apply H,
    rewrite -(add_halves n),
    apply rat.add_le_add_right,
    apply inv_ge_of_le Hm
  end

theorem rat_approx {s : seq} (H : regular s) :
        ∀ n : ℕ+, ∃ q : ℚ, s_le (s_abs (sadd s (sneg (const q)))) (const n⁻¹) :=
  begin
    intro m,
    rewrite ↑s_le,
    apply exists.elim (rat_approx_l1 H m),
    intro q Hq,
    apply exists.elim Hq,
    intro N HN,
    existsi q,
    apply nonneg_of_bdd_within,
    repeat (apply reg_add_reg | apply reg_neg_reg | apply abs_reg_of_reg | apply const_reg
             | assumption),
    intro n,
    existsi N,
    intro p Hp,
    rewrite ↑[sadd, sneg, s_abs, const],
    apply rat.le.trans,
    rotate 1,
    apply rat.sub_le_sub_left,
    apply HN,
    apply pnat.le.trans,
    apply Hp,
    rewrite -*pnat.mul.assoc,
    apply pnat.mul_le_mul_left,
    rewrite [sub_self, -neg_zero],
    apply neg_le_neg,
    apply rat.le_of_lt,
    apply inv_pos
  end

definition r_abs (s : reg_seq) : reg_seq :=
  reg_seq.mk (s_abs (reg_seq.sq s)) (abs_reg_of_reg (reg_seq.is_reg s))

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

theorem r_abs_well_defined {s t : reg_seq} (H : requiv s t) : requiv (r_abs s) (r_abs t) :=
  abs_well_defined (reg_seq.is_reg s) (reg_seq.is_reg t) H

theorem r_rat_approx (s : reg_seq) :
        ∀ n : ℕ+, ∃ q : ℚ, r_le (r_abs (radd s (rneg (r_const q)))) (r_const n⁻¹) :=
  rat_approx (reg_seq.is_reg s)

theorem const_bound {s : seq} (Hs : regular s) (n : ℕ+) :
        s_le (s_abs (sadd s (sneg (const (s n))))) (const n⁻¹) :=
  begin
    rewrite ↑[s_le, nonneg, s_abs, sadd, sneg, const],
    intro m,
    apply iff.mp !rat.le_add_iff_neg_le_sub_left,
    apply rat.le.trans,
    apply Hs,
    apply rat.add_le_add_right,
    rewrite -*pnat.mul.assoc,
    apply inv_ge_of_le,
    apply pnat.mul_le_mul_left
  end

theorem abs_const (a : ℚ) : const (abs a) ≡ s_abs (const a) :=
  begin
    rewrite [↑s_abs, ↑const],
    apply equiv.refl
  end

theorem r_abs_const (a : ℚ) : requiv (r_const (abs a) ) (r_abs (r_const a)) := abs_const a

theorem equiv_abs_of_ge_zero {s : seq} (Hs : regular s) (Hz : s_le zero s) : s_abs s ≡ s :=
  begin
    apply eq_of_bdd,
    apply abs_reg_of_reg Hs,
    apply Hs,
    intro j,
    rewrite ↑s_abs,
    let Hz' := s_nonneg_of_ge_zero Hs Hz,
    existsi 2 * j,
    intro n Hn,
    apply or.elim (decidable.em (s n ≥ 0)),
    intro Hpos,
    rewrite [rat.abs_of_nonneg Hpos, sub_self, abs_zero],
    apply rat.le_of_lt,
    apply inv_pos,
    intro Hneg,
    let Hneg' := lt_of_not_ge Hneg,
    have Hsn : -s n - s n > 0, from add_pos (neg_pos_of_neg Hneg') (neg_pos_of_neg Hneg'),
    rewrite [rat.abs_of_neg Hneg', rat.abs_of_pos Hsn],
    apply rat.le.trans,
    apply rat.add_le_add,
    repeat (apply rat.neg_le_neg; apply Hz'),
    rewrite *rat.neg_neg,
    apply rat.le.trans,
    apply rat.add_le_add,
    repeat (apply inv_ge_of_le; apply Hn),
    rewrite pnat.add_halves,
    apply rat.le.refl
  end

theorem equiv_neg_abs_of_le_zero {s : seq} (Hs : regular s) (Hz : s_le s zero) : s_abs s ≡ sneg s :=
  begin
    apply eq_of_bdd,
    apply abs_reg_of_reg Hs,
    apply reg_neg_reg Hs,
    intro j,
    rewrite [↑s_abs, ↑s_le at Hz],
    have Hz' : nonneg (sneg s), begin
      apply nonneg_of_nonneg_equiv,
      rotate 3,
      apply Hz,
      rotate 2,
      apply s_zero_add,
      repeat (apply Hs | apply zero_is_reg | apply reg_neg_reg | apply reg_add_reg)
    end,
    existsi 2 * j,
    intro n Hn,
    apply or.elim (decidable.em (s n ≥ 0)),
    intro Hpos,
    have Hsn : s n + s n ≥ 0, from add_nonneg Hpos Hpos,
    rewrite [rat.abs_of_nonneg Hpos, ↑sneg, rat.sub_neg_eq_add, rat.abs_of_nonneg Hsn],
    rewrite [↑nonneg at Hz', ↑sneg at Hz'],
    apply rat.le.trans,
    apply rat.add_le_add,
    repeat apply (rat.le_of_neg_le_neg !Hz'),
    apply rat.le.trans,
    apply rat.add_le_add,
    repeat (apply inv_ge_of_le; apply Hn),
    rewrite pnat.add_halves,
    apply rat.le.refl,
    intro Hneg,
    let Hneg' := lt_of_not_ge Hneg,
    rewrite [rat.abs_of_neg Hneg', ↑sneg, rat.sub_neg_eq_add, rat.neg_add_eq_sub, rat.sub_self,
                abs_zero],
    apply rat.le_of_lt,
    apply inv_pos
  end

theorem r_equiv_abs_of_ge_zero {s : reg_seq} (Hz : r_le r_zero s) : requiv (r_abs s) s :=
  equiv_abs_of_ge_zero (reg_seq.is_reg s) Hz

theorem r_equiv_neg_abs_of_le_zero {s : reg_seq} (Hz : r_le s r_zero) : requiv (r_abs s) (-s) :=
  equiv_neg_abs_of_le_zero (reg_seq.is_reg s) Hz

end s

namespace real
open [classes] s

theorem p_add_fractions (n : ℕ+) : (2 * n)⁻¹ + (2 * 3 * n)⁻¹ + (3 * n)⁻¹ = n⁻¹ :=
  assert T : 2⁻¹ + 2⁻¹ * 3⁻¹ + 3⁻¹ = 1, from dec_trivial,
  by rewrite[*inv_mul_eq_mul_inv,-*rat.right_distrib,T,rat.one_mul]

theorem rewrite_helper9 (a b c : ℝ) : b - c = (b - a) - (c - a) :=
  by rewrite[-sub_add_eq_sub_sub_swap,sub_add_cancel]

theorem rewrite_helper10 (a b c d : ℝ) : c - d = (c - a) + (a - b) + (b - d) :=
  by rewrite[*add_sub,*sub_add_cancel]

noncomputable definition rep (x : ℝ) : s.reg_seq := some (quot.exists_rep x)

definition re_abs (x : ℝ) : ℝ :=
  quot.lift_on x (λ a, quot.mk (s.r_abs a)) (take a b Hab, quot.sound (s.r_abs_well_defined Hab))

theorem r_abs_nonneg {x : ℝ} : zero ≤ x → re_abs x = x :=
  quot.induction_on x (λ a Ha, quot.sound  (s.r_equiv_abs_of_ge_zero Ha))

theorem r_abs_nonpos {x : ℝ} : x ≤ zero → re_abs x = -x :=
  quot.induction_on x (λ a Ha, quot.sound (s.r_equiv_neg_abs_of_le_zero Ha))

theorem abs_const' (a : ℚ) : of_rat (rat.abs a) = re_abs (of_rat a) := quot.sound (s.r_abs_const a)

theorem re_abs_is_abs : re_abs = real.abs := funext
  (begin
    intro x,
    apply eq.symm,
    let Hor := decidable.em (zero ≤ x),
    apply or.elim Hor,
    intro Hor1,
    rewrite [abs_of_nonneg Hor1, r_abs_nonneg Hor1],
    intro Hor2,
    have Hor2' : x ≤ zero, from le_of_lt (lt_of_not_ge Hor2),
    rewrite [abs_of_neg (lt_of_not_ge Hor2), r_abs_nonpos Hor2']
  end)

theorem abs_const (a : ℚ) : of_rat (rat.abs a) = abs (of_rat a) :=
  by rewrite -re_abs_is_abs -- ????

theorem rat_approx' (x : ℝ) : ∀ n : ℕ+, ∃ q : ℚ, re_abs (x - of_rat q) ≤ of_rat n⁻¹ :=
  quot.induction_on x (λ s n, s.r_rat_approx s n)

theorem rat_approx (x : ℝ) : ∀ n : ℕ+, ∃ q : ℚ, abs (x - of_rat q) ≤ of_rat n⁻¹ :=
  by rewrite -re_abs_is_abs; apply rat_approx'

noncomputable definition approx (x : ℝ) (n : ℕ+) := some (rat_approx x n)

theorem approx_spec (x : ℝ) (n : ℕ+) : abs (x - (of_rat (approx x n))) ≤ of_rat n⁻¹ :=
  some_spec (rat_approx x n)

theorem approx_spec' (x : ℝ) (n : ℕ+) : abs ((of_rat (approx x n)) - x) ≤ of_rat n⁻¹ :=
  by rewrite abs_sub; apply approx_spec

notation `r_seq` := ℕ+ → ℝ

noncomputable definition converges_to (X : r_seq) (a : ℝ) (N : ℕ+ → ℕ+) :=
  ∀ k : ℕ+, ∀ n : ℕ+, n ≥ N k → abs (X n - a) ≤ of_rat k⁻¹

noncomputable definition cauchy (X : r_seq) (M : ℕ+ → ℕ+) :=
  ∀ k : ℕ+, ∀ m n : ℕ+, m ≥ M k → n ≥ M k → abs (X m - X n) ≤ of_rat k⁻¹

theorem cauchy_of_converges_to {X : r_seq} {a : ℝ} {N : ℕ+ → ℕ+} (Hc : converges_to X a N) :
        cauchy X (λ k, N (2 * k)) :=
  begin
    intro k m n Hm Hn,
    rewrite (rewrite_helper9 a),
    apply le.trans,
    apply abs_add_le_abs_add_abs,
    apply le.trans,
    apply add_le_add,
    apply Hc,
    apply Hm,
    krewrite abs_neg,
    apply Hc,
    apply Hn,
    xrewrite of_rat_add,
    apply of_rat_le_of_rat_of_le,
    rewrite pnat.add_halves,
    apply rat.le.refl
  end

definition Nb (M : ℕ+ → ℕ+) := λ k, pnat.max (3 * k) (M (2 * k))

theorem Nb_spec_right (M : ℕ+ → ℕ+) (k : ℕ+) : M (2 * k) ≤ Nb M k := !max_right

theorem Nb_spec_left (M : ℕ+ → ℕ+) (k : ℕ+) : 3 * k ≤ Nb M k := !max_left

noncomputable definition lim_seq {X : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy X M) : ℕ+ → ℚ :=
  λ k, approx (X (Nb M k)) (2 * k)

theorem lim_seq_reg_helper {X : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy X M) {m n : ℕ+}
        (Hmn : M (2 * n) ≤M (2 * m)) :
           abs (of_rat (lim_seq Hc m) - X (Nb M m)) + abs (X (Nb M m) - X (Nb M n)) + abs
            (X (Nb M n) - of_rat (lim_seq Hc n)) ≤ of_rat (m⁻¹ + n⁻¹) :=
  begin
    apply le.trans,
    apply add_le_add_three,
    apply approx_spec',
    rotate 1,
    apply approx_spec,
    rotate 1,
    apply Hc,
    rotate 1,
    apply Nb_spec_right,
    rotate 1,
    apply pnat.le.trans,
    apply Hmn,
    apply Nb_spec_right,
    rewrite [*of_rat_add, rat.add.assoc, pnat.add_halves],
    apply of_rat_le_of_rat_of_le,
    apply rat.add_le_add_right,
    apply inv_ge_of_le,
    apply pnat.mul_le_mul_left
  end

theorem lim_seq_reg {X : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy X M) : s.regular (lim_seq Hc) :=
  begin
    rewrite ↑s.regular,
    intro m n,
    apply le_of_rat_le_of_rat,
    rewrite [abs_const, -of_rat_sub, (rewrite_helper10 (X (Nb M m)) (X (Nb M n)))],
    apply real.le.trans,
    apply abs_add_three,
    let Hor := decidable.em (M (2 * m) ≥ M (2 * n)),
    apply or.elim Hor,
    intro Hor1,
    apply lim_seq_reg_helper Hc Hor1,
    intro Hor2,
    let Hor2' := pnat.le_of_lt (pnat.lt_of_not_le Hor2),
    rewrite [real.abs_sub (X (Nb M n)), abs_sub (X (Nb M m)), abs_sub, -- ???
             rat.add.comm, add_comm_three],
    apply lim_seq_reg_helper Hc Hor2'
  end

theorem lim_seq_spec {X : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy X M) (k : ℕ+) :
        s.s_le (s.s_abs (s.sadd (lim_seq Hc) (s.sneg (s.const (lim_seq Hc k))) )) (s.const k⁻¹) :=
  begin
    apply s.const_bound,
    apply lim_seq_reg
  end

noncomputable definition r_lim_seq {X : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy X M) : s.reg_seq :=
  s.reg_seq.mk (lim_seq Hc) (lim_seq_reg Hc)

theorem r_lim_seq_spec {X : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy X M) (k : ℕ+) :
        s.r_le (s.r_abs (( s.radd (r_lim_seq Hc) (s.rneg (s.r_const ((s.reg_seq.sq (r_lim_seq Hc)) k)))))) (s.r_const (k)⁻¹) :=
  lim_seq_spec Hc k

noncomputable definition lim {X : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy X M) : ℝ :=
  quot.mk (r_lim_seq Hc)

theorem re_lim_spec {x : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy x M) (k : ℕ+) :
        re_abs ((lim Hc) - (of_rat ((lim_seq Hc) k))) ≤ of_rat k⁻¹ :=
  r_lim_seq_spec Hc k

theorem lim_spec' {x : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy x M) (k : ℕ+) :
        abs ((lim Hc) - (of_rat ((lim_seq Hc) k))) ≤ of_rat k⁻¹ :=
  by rewrite -re_abs_is_abs; apply re_lim_spec

theorem lim_spec {x : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy x M) (k : ℕ+) :
        abs ((of_rat ((lim_seq Hc) k)) - (lim Hc)) ≤ of_rat (k)⁻¹ :=
  by rewrite abs_sub; apply lim_spec'

theorem converges_of_cauchy {X : r_seq} {M : ℕ+ → ℕ+} (Hc : cauchy X M) :
        converges_to X (lim Hc) (Nb M) :=
  begin
    intro k n Hn,
    rewrite (rewrite_helper10 (X (Nb M n)) (of_rat (lim_seq Hc n))),
    apply le.trans,
    apply abs_add_three,
    apply le.trans,
    apply add_le_add_three,
    apply Hc,
    apply pnat.le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply Nb_spec_right,
    have HMk : M (2 * k) ≤ Nb M n, begin
      apply pnat.le.trans,
      apply Nb_spec_right,
      apply pnat.le.trans,
      apply Hn,
      apply pnat.le.trans,
      apply mul_le_mul_left 3,
      apply Nb_spec_left
    end,
    apply HMk,
    rewrite ↑lim_seq,
    apply approx_spec,
    apply lim_spec,
    rewrite 2 of_rat_add,
    apply of_rat_le_of_rat_of_le,
    apply rat.le.trans,
    apply rat.add_le_add_three,
    apply rat.le.refl,
    apply inv_ge_of_le,
    apply pnat_mul_le_mul_left',
    apply pnat.le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply Nb_spec_left,
    apply inv_ge_of_le,
    apply pnat.le.trans,
    rotate 1,
    apply Hn,
    rotate_right 1,
    apply Nb_spec_left,
    rewrite [-*pnat.mul.assoc, p_add_fractions],
    apply rat.le.refl
  end


--------------------------------------------------
-- supremum property
-- this development roughly follows the proof of completeness done in Isabelle.

section supremum
open prod nat
local postfix `~` := nat_of_pnat

local notation 2 := (1 : ℚ) + 1
parameter X : ℝ → Prop

definition rpt {A : Type} (op : A → A) : ℕ → A → A
 | rpt 0 := λ a, a
 | rpt (succ k) := λ a, op (rpt k a)


definition ub (x : ℝ) := ∀ y : ℝ, X y → y ≤ x
definition bounded := ∃ x : ℝ, ub x
definition sup (x : ℝ) := ub x ∧ ∀ y : ℝ, ub y → x ≤ y

parameter elt : ℝ
hypothesis inh :  X elt
parameter bound : ℝ
hypothesis bdd : ub bound

parameter floor : ℝ → int
parameter ceil : ℝ → int
hypothesis floor_spec : ∀ x : ℝ, of_rat (of_int (floor x)) ≤ x
hypothesis ceil_spec : ∀ x : ℝ, of_rat (of_int (ceil x)) ≥ x
hypothesis floor_succ : ∀ x : ℝ, int.lt (floor (x - 1)) (floor x)
hypothesis ceil_succ : ∀ x : ℝ, int.lt (ceil x) (ceil (x + 1))

include inh bdd floor_spec ceil_spec floor_succ ceil_succ


-- this should exist somewhere, no? I can't find it
theorem not_forall_of_exists_not {A : Type} {P : A → Prop} (H : ∃ a : A, ¬ P a) :
        ¬ ∀ a : A, P a :=
  begin
    intro Hall,
    cases H with [a, Ha],
    apply Ha (Hall a)
  end

definition avg (a b : ℚ) := a / 2 + b / 2

definition bisect (ab : ℚ × ℚ) :=
  if ub (avg (pr1 ab) (pr2 ab)) then
    (pr1 ab, (avg (pr1 ab) (pr2 ab)))
  else
    (avg (pr1 ab) (pr2 ab), pr2 ab)

set_option pp.coercions true

definition under : ℚ := of_int (floor (elt - 1))

theorem under_spec1 : of_rat under < elt :=
  let fs := floor_succ in
  have H : of_rat under < of_rat (of_int (floor elt)), begin
    apply of_rat_lt_of_rat_of_lt,
    apply iff.mpr !of_int_lt_of_int,
    apply fs
  end,
  lt_of_lt_of_le H !floor_spec

theorem under_spec : ¬ ub under :=
  using inh,
  using floor_spec,
  using floor_succ,
  begin
    rewrite ↑ub,
    apply not_forall_of_exists_not,
    existsi elt,
    apply iff.mpr not_implies_iff_and_not,
    apply and.intro,
    apply inh,
    apply not_le_of_gt under_spec1
  end

definition over : ℚ := of_int (ceil (bound + 1)) -- b

theorem over_spec1 : bound < of_rat over :=
  let cs := ceil_succ in
  have H : of_rat (of_int (ceil bound)) < of_rat over, begin
    apply of_rat_lt_of_rat_of_lt,
    apply iff.mpr !of_int_lt_of_int,
    apply cs
  end,
  lt_of_le_of_lt !ceil_spec H

theorem over_spec : ub over :=
  using bdd,
  using ceil_spec,
  using ceil_succ,
  begin
    rewrite ↑ub,
    intro y Hy,
    apply le_of_lt,
    apply lt_of_le_of_lt,
    apply bdd,
    apply Hy,
    apply over_spec1
  end

definition under_seq := λ n : ℕ, pr1 (rpt bisect n (under, over)) -- A

definition over_seq := λ n : ℕ, pr2 (rpt bisect n (under, over)) -- B

definition avg_seq := λ n : ℕ, avg (over_seq n) (under_seq n) -- C

theorem avg_symm (n : ℕ) : avg_seq n = avg (under_seq n) (over_seq n) :=
  by rewrite [↑avg_seq, ↑avg, rat.add.comm]

theorem over_0 : over_seq 0 = over := rfl
theorem under_0 : under_seq 0 = under := rfl

theorem succ_helper (n : ℕ) : avg (pr1 (rpt bisect n (under, over))) (pr2 (rpt bisect n (under, over))) = avg_seq n :=
   by rewrite avg_symm

theorem under_succ (n : ℕ) : under_seq (succ n) =
        (if ub (avg_seq n) then under_seq n else avg_seq n) :=
  begin
    cases (decidable.em (ub (avg_seq n))) with [Hub, Hub],
    rewrite [if_pos Hub],
    have H :  pr1 (bisect (rpt bisect n (under, over))) = under_seq n, by
      rewrite [↑under_seq, ↑bisect at {2}, -succ_helper at Hub, if_pos Hub],
    apply H,
    rewrite [if_neg Hub],
    have H : pr1 (bisect (rpt bisect n (under, over))) = avg_seq n, by
      rewrite [↑bisect at {2}, -succ_helper at Hub, if_neg Hub, avg_symm],
    apply H
  end

theorem over_succ (n : ℕ) : over_seq (succ n) =
        (if ub (avg_seq n) then avg_seq n else over_seq n) :=
  begin
    cases (decidable.em (ub (avg_seq n))) with [Hub, Hub],
    rewrite [if_pos Hub],
    have H : pr2 (bisect (rpt bisect n (under, over))) = avg_seq n, by
      rewrite [↑bisect at {2}, -succ_helper at Hub, if_pos Hub, avg_symm],
    apply H,
    rewrite [if_neg Hub],
    have H : pr2 (bisect (rpt bisect n (under, over))) = over_seq n, by
      rewrite [↑over_seq, ↑bisect at {2}, -succ_helper at Hub, if_neg Hub],
    apply H
  end

-- rat.pow_zero refers to algebra.pow?
theorem rat.pow_zero (a : ℚ) : rat.pow a 0 = 1 := sorry

theorem rat.pow_pos {a : ℚ} (H : a > 0) (n : ℕ) : rat.pow a n > 0 := sorry

theorem rat.pow_one (a : ℚ) : rat.pow a 1 = a := sorry

theorem rat.pow_add (a : ℚ) (m : ℕ) : ∀ n, rat.pow a (m + n) = rat.pow a m * rat.pow a n := sorry

theorem div_two_sub_self (a : ℚ) : a / 2 - a = - (a / 2) := sorry

theorem sub_self_div_two (a : ℚ) : a - a / 2 = a / 2 := sorry

theorem rat.div_sub_div_same (a b c : ℚ) : (a / c) - (b / c) = (a - b) / c := sorry

theorem width (n : ℕ) : over_seq n - under_seq n = (over - under) / (rat.pow 2 n) :=
  nat.induction_on n
    (by rewrite [over_0, under_0, rat.pow_zero, rat.div_one])
    (begin
      intro a Ha,
      rewrite [over_succ, under_succ],
      let Hou := calc
        (over_seq a) / 2 - (under_seq a) / 2 = ((over - under) / rat.pow 2 a) / 2 : by rewrite [rat.div_sub_div_same, Ha]
        ... = (over - under) / (rat.pow 2 a * 2) : rat.div_div_eq_div_mul (rat.ne_of_gt (rat.pow_pos dec_trivial _)) dec_trivial
        ... = (over - under) / rat.pow 2 (a + 1) : by rewrite  rat.pow_add,
      cases (decidable.em (ub (avg_seq a))),
      rewrite [*if_pos a_1, -add_one, -Hou, ↑avg_seq, ↑avg, rat.add.assoc, div_two_sub_self],
      rewrite [*if_neg a_1, -add_one, -Hou, ↑avg_seq, ↑avg, rat.sub_add_eq_sub_sub, sub_self_div_two]
    end)



theorem binary_nat_bound (a : ℕ) : of_nat a ≤ (rat.pow 2 a) :=
  nat.induction_on a (rat.zero_le_one) (begin apply sorry end)

theorem binary_bound (a : ℚ) : ∃ n : ℕ, a ≤ rat.pow 2 n :=
  exists.intro (ubound a) (calc
      a ≤ of_nat (ubound a) : ubound_ge
    ... ≤ rat.pow 2 (ubound a) : binary_nat_bound)

theorem rat_of_pnat_add {k : ℕ} (H : succ k > 0) : rat_of_pnat (subtype.tag (succ k) H) = (rat.of_nat k) + 1 := sorry

theorem rat_power_two_le (k : ℕ+) : rat_of_pnat k ≤ rat.pow 2 k~ :=
  begin
  apply subtype.rec_on k,
  intros n Hn,
  induction n,
  apply absurd Hn !nat.not_lt_self,
  rewrite (rat_of_pnat_add Hn),
  apply sorry
  end

theorem width_narrows : ∃ n : ℕ, over_seq n - under_seq n ≤ 1 :=
  begin
    cases binary_bound (over - under) with [a, Ha],
    existsi a,
    rewrite (width a),
    apply rat.div_le_of_le_mul,
    apply rat.pow_pos dec_trivial,
    rewrite rat.mul_one,
    apply Ha
  end

definition over' := over_seq (some width_narrows)

definition under' := under_seq (some width_narrows)

definition over_seq' := λ n, over_seq (n + some width_narrows)

definition under_seq' := λ n, under_seq (n + some width_narrows)

theorem width' (n : ℕ) : over_seq' n - under_seq' n ≤ 1 / rat.pow 2 n := sorry

--theorem twos (y r : ℚ) (H : 0 < r) : ∃ n : ℕ, y / (rat.pow 2 n) < r := sorry

theorem PA (n : ℕ) : ¬ ub (under_seq n) :=
  nat.induction_on n
    (by rewrite under_0; apply under_spec)
    (begin
      intro a Ha,
      rewrite under_succ,
      cases (decidable.em (ub (avg_seq a))),
      rewrite (if_pos a_1),
      assumption,
      rewrite (if_neg a_1),
      assumption
    end)

theorem PB (n : ℕ) : ub (over_seq n) :=
  nat.induction_on n
    (by rewrite over_0; apply over_spec)
    (begin
      intro a Ha,
      rewrite over_succ,
      cases (decidable.em (ub (avg_seq a))),
      rewrite (if_pos a_1),
      assumption,
      rewrite (if_neg a_1),
      assumption
    end)

theorem under_lt_over : under < over :=
  begin
    cases (exists_not_of_not_forall under_spec) with [x, Hx],
    cases ((iff.mp not_implies_iff_and_not) Hx) with [HXx, Hxu],
    apply lt_of_rat_lt_of_rat,
    apply lt_of_lt_of_le,
    apply lt_of_not_ge Hxu,
    apply over_spec _ HXx
  end

theorem under_seq_lt_over_seq : ∀ m n : ℕ, under_seq m < over_seq n :=
  begin
    intros,
    cases (exists_not_of_not_forall (PA m)) with [x, Hx],
    cases ((iff.mp not_implies_iff_and_not) Hx) with [HXx, Hxu],
    apply lt_of_rat_lt_of_rat,
    apply lt_of_lt_of_le,
    apply lt_of_not_ge Hxu,
    apply PB,
    apply HXx
  end

theorem under_seq_lt_over_seq_single : ∀ n : ℕ, under_seq n < over_seq n :=
  by intros; apply under_seq_lt_over_seq

theorem under_seq'_lt_over_seq' : ∀ m n : ℕ, under_seq' m < over_seq' n :=
  by intros; apply under_seq_lt_over_seq

theorem under_seq'_lt_over_seq'_single : ∀ n : ℕ, under_seq' n < over_seq' n :=
  by intros; apply under_seq_lt_over_seq

--theorem over_dist (n : ℕ) : abs (over - over_seq n) ≤ (over - under) / rat.pow 2 n := sorry

theorem under_seq_mono_helper (i k : ℕ) : under_seq i ≤ under_seq (i + k) :=
  (nat.induction_on k
    (by rewrite nat.add_zero; apply rat.le.refl)
    (begin
      intros a Ha,
      rewrite [add_succ, under_succ],
      cases (decidable.em (ub (avg_seq (i + a)))) with [Havg, Havg],
      rewrite (if_pos Havg),
      apply Ha,
      rewrite [if_neg Havg, ↑avg_seq, ↑avg],
      apply rat.le.trans,
      apply Ha,
      rewrite -rat.add_halves at {1},
      apply rat.add_le_add_right,
      apply rat.div_le_div_of_le_of_pos,
      apply rat.le_of_lt,
      apply under_seq_lt_over_seq,
      apply dec_trivial
    end))

theorem under_seq_mono (i j : ℕ) (H : i ≤ j) : under_seq i ≤ under_seq j :=
  begin
    cases le.elim H with [k, Hk'],
    rewrite -Hk',
    apply under_seq_mono_helper
  end

theorem over_seq_mono_helper (i k : ℕ) : over_seq (i + k) ≤ over_seq i :=
  nat.induction_on k
    (by rewrite nat.add_zero; apply rat.le.refl)
    (begin
      intros a Ha,
      rewrite [add_succ, over_succ],
      cases (decidable.em (ub (avg_seq (i + a)))) with [Havg, Havg],
      rewrite [if_pos Havg, ↑avg_seq, ↑avg],
      apply rat.le.trans,
      rotate 1,
      apply Ha,
      rotate 1,
      rewrite -{over_seq (i + a)}rat.add_halves at {2},
      apply rat.add_le_add_left,
      apply rat.div_le_div_of_le_of_pos,
      apply rat.le_of_lt,
      apply under_seq_lt_over_seq,
      apply dec_trivial,
      rewrite [if_neg Havg],
      apply Ha
    end)

theorem over_seq_mono (i j : ℕ) (H : i ≤ j) : over_seq j ≤ over_seq i :=
  begin
    cases le.elim H with [k, Hk'],
    rewrite -Hk',
    apply over_seq_mono_helper
  end



theorem rat_power_two_inv_ge (k : ℕ+) : 1 / rat.pow 2 k~ ≤ k⁻¹ :=
  rat.div_le_div_of_le !rat_of_pnat_is_pos !rat_power_two_le

open s
theorem regular_lemma_helper {s : seq} {m n : ℕ+} (Hm : m ≤ n)
        (H : ∀ n i : ℕ+, i ≥ n → under_seq' n~ ≤ s i ∧ s i ≤ over_seq' n~) :
        rat.abs (s m - s n) ≤ m⁻¹ + n⁻¹ :=
  begin
    cases (H m n Hm) with [T1under, T1over],
    cases (H m m (!pnat.le.refl)) with [T2under, T2over],
    apply rat.le.trans,
    apply rat.dist_bdd_within_interval,
    apply under_seq'_lt_over_seq'_single,
    rotate 1,
    repeat assumption,
    apply rat.le.trans,
    apply width',
    apply rat.le.trans,
    apply rat_power_two_inv_ge,
    apply rat.le_add_of_nonneg_right,
    apply rat.le_of_lt (!inv_pos)
  end

theorem regular_lemma (s : seq) (H : ∀ n i : ℕ+, i ≥ n → under_seq' n~ ≤ s i ∧ s i ≤ over_seq' n~) :
        regular s :=
  begin
    rewrite ↑regular,
    intros,
    cases (decidable.em (m ≤ n)) with [Hm, Hn],
    apply regular_lemma_helper Hm H,
    let T := regular_lemma_helper (pnat.le_of_lt (pnat.lt_of_not_le Hn)) H,
    rewrite [rat.abs_sub at T, {n⁻¹ + _}rat.add.comm at T],
    exact T
  end

definition p_under_seq : seq := λ n : ℕ+, under_seq' n~

definition p_over_seq : seq := λ n : ℕ+, over_seq' n~

theorem under_seq_regular : regular p_under_seq :=
  begin
    apply regular_lemma,
    intros n i Hni,
    apply and.intro,
    apply under_seq_mono,
    apply nat.add_le_add_right Hni,
    apply rat.le_of_lt,
    apply under_seq_lt_over_seq
  end

theorem over_seq_regular : regular p_over_seq :=
  begin
    apply regular_lemma,
    intros n i Hni,
    apply and.intro,
    apply rat.le_of_lt,
    apply under_seq_lt_over_seq,
    apply over_seq_mono,
    apply nat.add_le_add_right Hni
  end

definition sup_over : ℝ := quot.mk (reg_seq.mk p_over_seq over_seq_regular)

definition sup_under : ℝ := quot.mk (reg_seq.mk p_under_seq under_seq_regular)

theorem over_bound : ub sup_over :=
  begin
    rewrite ↑ub,
    intros y Hy,
    apply le_of_le_reprs,
    intro n,
    apply PB,
    apply Hy
  end

theorem under_lowest_bound : ∀ y : ℝ, ub y → sup_under ≤ y :=
  begin
    intros y Hy,
    apply le_of_reprs_le,
    intro n,
    cases (exists_not_of_not_forall (PA _)) with [x, Hx],
    cases (iff.mp not_implies_iff_and_not Hx) with [HXx, Hxn],
    apply le.trans,
    apply le_of_lt,
    apply lt_of_not_ge Hxn,
    apply Hy,
    apply HXx
  end

theorem under_over_equiv : p_under_seq ≡ p_over_seq :=
  begin
    rewrite ↑equiv,
    intros,
    apply rat.le.trans,
    have H : p_under_seq n < p_over_seq n, from !under_seq_lt_over_seq,
    rewrite [rat.abs_of_neg (iff.mpr !rat.sub_neg_iff_lt H), rat.neg_sub],
    apply width',
    apply rat.le.trans,
    apply rat_power_two_inv_ge,
    apply rat.le_add_of_nonneg_left,
    apply rat.le_of_lt !inv_pos
  end

theorem under_over_eq : sup_under = sup_over := quot.sound under_over_equiv

theorem supremum_of_complete : ∃ x : ℝ, sup x :=
  exists.intro sup_over (and.intro over_bound (under_over_eq ▸ under_lowest_bound))

end supremum

end real
