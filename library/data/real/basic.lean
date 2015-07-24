/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
The real numbers, constructed as equivalence classes of Cauchy sequences of rationals.
This construction follows Bishop and Bridges (1985).

To do:
 o Break positive naturals into their own file
 o Rename things and possibly make theorems private
-/

import data.nat data.rat.order data.pnat
open nat eq eq.ops pnat
open -[coercions] rat
local notation 0 := rat.of_num 0
local notation 1 := rat.of_num 1
----------------------------------------------------------------------------------------------------

-------------------------------------
-- theorems to add to (ordered) field and/or rat

-- this can move to pnat
theorem find_midpoint {a b : ℚ} (H : a > b) : ∃ c : ℚ, a > b + c ∧ c > 0 :=
  exists.intro ((a - b) / (1 + 1))
    (and.intro (assert H2 : a + a > (b + b) + (a - b), from calc
      a + a > b + a : rat.add_lt_add_right H
      ... = b + a + b - b : rat.add_sub_cancel
      ... = b + b + a - b : rat.add.right_comm
      ... = (b + b) + (a - b) : add_sub,
     assert H3 : (a + a) / (1 + 1) > ((b + b) + (a - b)) / (1 + 1),
       from div_lt_div_of_lt_of_pos H2 dec_trivial,
     by rewrite [div_two at H3, -div_add_div_same at H3, div_two at H3]; exact H3)
    (pos_div_of_pos_of_pos (iff.mpr !sub_pos_iff_lt H) dec_trivial))

theorem add_sub_comm (a b c d : ℚ) : a + b - (c + d) = (a - c) + (b - d) :=
  calc
     a + b - (c + d) = a + b - c - d   : sub_add_eq_sub_sub
                 ... = a - c + b - d   : sub_add_eq_add_sub
                 ... = a - c + (b - d) : add_sub

theorem s_mul_assoc_lemma_4 {n : ℕ+} {ε q : ℚ} (Hε : ε > 0) (Hq : q > 0) (H : n ≥ pceil (q / ε)) :
        q * n⁻¹ ≤ ε :=
  begin
    let H2 := pceil_helper H (pos_div_of_pos_of_pos Hq Hε),
    let H3 := mul_le_of_le_div (pos_div_of_pos_of_pos Hq Hε) H2,
    rewrite -(one_mul ε),
    apply mul_le_mul_of_mul_div_le,
    repeat assumption
  end

-------------------------------------
-- small helper lemmas

theorem s_mul_assoc_lemma_3 (a b n : ℕ+) (p : ℚ) :
        p * ((a * n)⁻¹ + (b * n)⁻¹) = p * (a⁻¹ + b⁻¹) * n⁻¹ :=
  by rewrite [rat.mul.assoc, rat.right_distrib, *inv_mul_eq_mul_inv]

theorem find_thirds (a b : ℚ) (H : b > 0) : ∃ n : ℕ+, a + n⁻¹ + n⁻¹ + n⁻¹ < a + b :=
  let n := pceil (of_nat 4 / b) in
  have of_nat 3 * n⁻¹ < b, from calc
   of_nat 3 * n⁻¹ < of_nat 4 * n⁻¹
                  : rat.mul_lt_mul_of_pos_right dec_trivial !inv_pos
              ... ≤ of_nat 4 * (b / of_nat 4)
                  : rat.mul_le_mul_of_nonneg_left (!inv_pceil_div dec_trivial H) !of_nat_nonneg
              ... = b / of_nat 4 * of_nat 4 : rat.mul.comm
              ... = b : rat.div_mul_cancel dec_trivial,
  exists.intro n (calc
    a + n⁻¹ + n⁻¹ + n⁻¹ = a + (1 + 1 + 1) * n⁻¹ : by rewrite[*rat.right_distrib,*rat.one_mul,-*rat.add.assoc]
                    ... = a + of_nat 3 * n⁻¹    : {show 1+1+1=of_nat 3, from dec_trivial}
                    ... < a + b                 : rat.add_lt_add_left this a)

theorem squeeze {a b : ℚ} (H : ∀ j : ℕ+, a ≤ b + j⁻¹ + j⁻¹ + j⁻¹) : a ≤ b :=
  begin
    apply rat.le_of_not_gt,
    intro Hb,
    apply (exists.elim (find_midpoint Hb)),
    intro c Hc,
    apply (exists.elim (find_thirds b c (and.right Hc))),
    intro j Hbj,
    have Ha : a > b + j⁻¹ + j⁻¹ + j⁻¹, from lt.trans Hbj (and.left Hc),
    exact absurd !H (not_le_of_gt Ha)
  end

theorem squeeze_2 {a b : ℚ} (H : ∀ ε : ℚ, ε > 0 → a ≥ b - ε) : a ≥ b :=
  begin
    apply rat.le_of_not_gt,
    intro Hb,
    apply (exists.elim (find_midpoint Hb)),
    intro c Hc,
    let Hc' := H c (and.right Hc),
    apply (rat.not_le_of_gt (and.left Hc)) (iff.mpr !le_add_iff_sub_right_le Hc')
  end

theorem rewrite_helper (a b c d : ℚ) : a * b  - c * d = a * (b - d) + (a - c) * d :=
  by rewrite[rat.mul_sub_left_distrib, rat.mul_sub_right_distrib, add_sub, rat.sub_add_cancel]

theorem rewrite_helper3 (a b c d e f g: ℚ) : a * (b + c) - (d * e + f * g) =
        (a * b - d * e) + (a * c - f * g) :=
  by rewrite[rat.mul.left_distrib, add_sub_comm]

theorem rewrite_helper4 (a b c d : ℚ) : a * b - c * d = (a * b - a * d) + (a * d - c * d) :=
  by rewrite[add_sub, rat.sub_add_cancel]

theorem rewrite_helper5 (a b x y : ℚ) : a - b = (a - x) + (x - y) + (y - b) :=
  by rewrite[*add_sub, *rat.sub_add_cancel]

theorem rewrite_helper7 (a b c d x : ℚ) :
        a * b * c - d = (b * c) * (a - x) + (x * b * c - d) :=
  by rewrite[rat.mul_sub_left_distrib, add_sub]; exact (calc
     a * b * c - d = a * b * c - x * b * c + x * b * c - d : rat.sub_add_cancel
           ... = b * c * a - b * c * x + x * b * c - d :
       have ∀ {a b c : ℚ}, a * b * c = b * c * a, from
         λa b c, !rat.mul.comm ▸ !rat.mul.right_comm,
       this ▸ this ▸ rfl)

theorem ineq_helper (a b : ℚ) (k m n : ℕ+) (H : a ≤ (k * 2 * m)⁻¹ + (k * 2 * n)⁻¹)
                    (H2 : b ≤ (k * 2 * m)⁻¹ + (k * 2 * n)⁻¹) :
        (rat_of_pnat k) * a + b * (rat_of_pnat k) ≤ m⁻¹ + n⁻¹ :=
  have (k * 2 * m)⁻¹ + (k * 2 * n)⁻¹ = (2 * k)⁻¹ * (m⁻¹ + n⁻¹),
    by rewrite[rat.mul.left_distrib,*inv_mul_eq_mul_inv]; exact !rat.mul.comm ▸ rfl,
  have a + b ≤ k⁻¹ * (m⁻¹ + n⁻¹), from calc
   a + b ≤ (2 * k)⁻¹ * (m⁻¹ + n⁻¹) + (2 * k)⁻¹ * (m⁻¹ + n⁻¹) : rat.add_le_add (this ▸ H) (this ▸ H2)
     ... = ((2 * k)⁻¹ + (2 * k)⁻¹) * (m⁻¹ + n⁻¹) : rat.mul.right_distrib
     ... = k⁻¹ * (m⁻¹ + n⁻¹) : (pnat.add_halves k) ▸ rfl,
  calc (rat_of_pnat k) * a + b * (rat_of_pnat k)
         = (rat_of_pnat k) * a + (rat_of_pnat k) * b : rat.mul.comm
     ... = (rat_of_pnat k) * (a + b) : rat.left_distrib
     ... ≤ (rat_of_pnat k) * (k⁻¹ * (m⁻¹ + n⁻¹)) :
             iff.mp (!rat.le_iff_mul_le_mul_left !rat_of_pnat_is_pos) this
     ... = m⁻¹ + n⁻¹ : by rewrite[-rat.mul.assoc, inv_cancel_left, rat.one_mul]

theorem factor_lemma (a b c d e : ℚ) : abs (a + b + c - (d + (b + e))) = abs ((a - d) + (c - e)) :=
  !congr_arg (calc
    a + b + c - (d + (b + e)) = a + b + c - (d + b + e)   : rat.add.assoc
                         ...  = a + b - (d + b) + (c - e) : add_sub_comm
                         ...  = a + b - b - d + (c - e)   : sub_add_eq_sub_sub_swap
                         ...  = a - d + (c - e)           : rat.add_sub_cancel)

theorem factor_lemma_2 (a b c d : ℚ) : (a + b) + (c + d) = (a + c) + (d + b) :=
  !rat.add.comm ▸ (binary.comm4 rat.add.comm rat.add.assoc a b c d)

--------------------------------------
-- define cauchy sequences and equivalence. show equivalence actually is one
namespace s

notation `seq` := ℕ+ → ℚ

definition regular (s : seq) := ∀ m n : ℕ+, abs (s m - s n) ≤ m⁻¹ + n⁻¹

definition equiv (s t : seq) := ∀ n : ℕ+, abs (s n - t n) ≤ n⁻¹ + n⁻¹
infix `≡` := equiv

theorem equiv.refl (s : seq) : s ≡ s :=
  begin
    rewrite ↑equiv,
    intros,
    rewrite [rat.sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem equiv.symm (s t : seq) (H : s ≡ t) : t ≡ s :=
  begin
    rewrite ↑equiv at *,
    intros,
    rewrite [-abs_neg, neg_sub],
    exact H n
  end

theorem bdd_of_eq {s t : seq} (H : s ≡ t) :
        ∀ j : ℕ+, ∀ n : ℕ+, n ≥ 2 * j → abs (s n - t n) ≤ j⁻¹ :=
  begin
    rewrite ↑equiv at *,
    intros [j, n, Hn],
    apply rat.le.trans,
    apply H n,
    rewrite -(add_halves j),
    apply rat.add_le_add,
    apply inv_ge_of_le Hn,
    apply inv_ge_of_le Hn
  end

theorem eq_of_bdd {s t : seq} (Hs : regular s) (Ht : regular t)
        (H : ∀ j : ℕ+, ∃ Nj : ℕ+, ∀ n : ℕ+, Nj ≤ n → abs (s n - t n) ≤ j⁻¹) : s ≡ t :=
  begin
    rewrite ↑equiv,
    intros,
    have Hj : (∀ j : ℕ+, abs (s n - t n) ≤ n⁻¹ + n⁻¹ + j⁻¹ + j⁻¹ + j⁻¹), begin
      intros,
      apply exists.elim (H j),
      intros [Nj, HNj],
      rewrite [-(rat.sub_add_cancel (s n) (s (max j Nj))), rat.add.assoc (s n + -s (max j Nj)),
              ↑regular at *],
      apply rat.le.trans,
      apply abs_add_le_abs_add_abs,
      apply rat.le.trans,
      apply rat.add_le_add,
      apply Hs,
      rewrite [-(rat.sub_add_cancel (s (max j Nj)) (t (max j Nj))), rat.add.assoc],
      apply abs_add_le_abs_add_abs,
      apply rat.le.trans,
      apply rat.add_le_add_left,
      apply rat.add_le_add,
      apply HNj (max j Nj) (max_right j Nj),
      apply Ht,
      have hsimp : ∀ m : ℕ+, n⁻¹ + m⁻¹ + (j⁻¹ + (m⁻¹ + n⁻¹)) = n⁻¹ + n⁻¹ + j⁻¹ + (m⁻¹ + m⁻¹),
        from λm, calc
           n⁻¹ + m⁻¹ + (j⁻¹ + (m⁻¹ + n⁻¹)) = n⁻¹ + (j⁻¹ + (m⁻¹ + n⁻¹)) + m⁻¹ : rat.add.right_comm
                                       ... = n⁻¹ + (j⁻¹ + m⁻¹ + n⁻¹) + m⁻¹   : rat.add.assoc
                                       ... = n⁻¹ + (n⁻¹ + (j⁻¹ + m⁻¹)) + m⁻¹ : rat.add.comm
                                       ... = n⁻¹ + n⁻¹ + j⁻¹ + (m⁻¹ + m⁻¹)   : by rewrite[-*rat.add.assoc],
      rewrite hsimp,
      have Hms : (max j Nj)⁻¹ + (max j Nj)⁻¹ ≤ j⁻¹ + j⁻¹, begin
        apply rat.add_le_add,
        apply inv_ge_of_le (max_left j Nj),
        apply inv_ge_of_le (max_left j Nj),
      end,
     apply (calc
       n⁻¹ + n⁻¹ + j⁻¹ + ((max j Nj)⁻¹ + (max j Nj)⁻¹) ≤ n⁻¹ + n⁻¹ + j⁻¹ + (j⁻¹ + j⁻¹) :
         rat.add_le_add_left Hms
       ... = n⁻¹ + n⁻¹ + j⁻¹ + j⁻¹ + j⁻¹ : by rewrite *rat.add.assoc)
    end,
    apply (squeeze Hj)
  end

theorem eq_of_bdd_var {s t : seq} (Hs : regular s) (Ht : regular t)
        (H : ∀ ε : ℚ, ε > 0 → ∃ Nj : ℕ+, ∀ n : ℕ+, Nj ≤ n → abs (s n - t n) ≤ ε) : s ≡ t :=
  begin
    apply eq_of_bdd,
    apply Hs,
    apply Ht,
    intros,
    apply H j⁻¹,
    apply inv_pos
  end

set_option pp.beta false
theorem pnat_bound {ε : ℚ} (Hε : ε > 0) : ∃ p : ℕ+, p⁻¹ ≤ ε :=
  begin
    existsi (pceil (1 / ε)),
    rewrite -(rat.div_div (rat.ne_of_gt Hε)) at {2},
    apply pceil_helper,
    apply le.refl,
    apply div_pos_of_pos Hε
  end

theorem bdd_of_eq_var {s t : seq} (Hs : regular s) (Ht : regular t) (Heq : s ≡ t) :
        ∀ ε : ℚ, ε > 0 → ∃ Nj : ℕ+, ∀ n : ℕ+, Nj ≤ n → abs (s n - t n) ≤ ε :=
  begin
    intro ε Hε,
    apply (exists.elim (pnat_bound Hε)),
    intro N HN,
    let Bd' := bdd_of_eq Heq N,
    existsi 2 * N,
    intro n Hn,
    apply rat.le.trans,
    apply Bd' n Hn,
    assumption
  end

theorem equiv.trans (s t u : seq) (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (H : s ≡ t) (H2 : t ≡ u) : s ≡ u :=
  begin
    apply eq_of_bdd Hs Hu,
    intros,
    existsi 2 * (2 * j),
    intro n Hn,
    rewrite [-rat.sub_add_cancel (s n) (t n), rat.add.assoc],
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    have Hst : abs (s n - t n) ≤ (2 * j)⁻¹, from bdd_of_eq H _ _ Hn,
    have Htu : abs (t n - u n) ≤ (2 * j)⁻¹, from bdd_of_eq H2 _ _ Hn,
    rewrite -(add_halves j),
    apply rat.add_le_add,
    repeat assumption
  end

-----------------------------------
-- define operations on cauchy sequences. show operations preserve regularity

definition K (s : seq) : ℕ+ := pnat.pos (ubound (abs (s pone)) + 1 + 1) dec_trivial

theorem canon_bound {s : seq} (Hs : regular s) (n : ℕ+) : abs (s n) ≤ rat_of_pnat (K s) :=
  calc
    abs (s n) = abs (s n - s pone + s pone) : by rewrite rat.sub_add_cancel
    ... ≤ abs (s n - s pone) + abs (s pone) : abs_add_le_abs_add_abs
    ... ≤ n⁻¹ + pone⁻¹ + abs (s pone) : rat.add_le_add_right !Hs
    ... = n⁻¹ + (1 + abs (s pone)) : by rewrite [pone_inv, rat.add.assoc]
    ... ≤ 1 + (1 + abs (s pone)) : rat.add_le_add_right (inv_le_one n)
    ... = abs (s pone) + (1 + 1) :
      by rewrite [add.comm 1 (abs (s pone)), rat.add.comm 1, rat.add.assoc]
    ... ≤ of_nat (ubound (abs (s pone))) + (1 + 1) : rat.add_le_add_right (!ubound_ge)
    ... = of_nat (ubound (abs (s pone)) + (1 + 1)) : of_nat_add
    ... = of_nat (ubound (abs (s pone)) + 1 + 1) : nat.add.assoc

definition K₂ (s t : seq) := max (K s) (K t)

theorem K₂_symm (s t : seq) : K₂ s t = K₂ t s :=
  if H : K s < K t then
    (assert H1 : K₂ s t = K t, from max_eq_right H,
     assert H2 : K₂ t s = K t, from max_eq_left (not_lt_of_ge (le_of_lt H)),
     by rewrite [H1, -H2])
  else
    (assert H1 : K₂ s t = K s, from max_eq_left H,
      if J : K t < K s then
        (assert H2 : K₂ t s = K s, from max_eq_right J, by rewrite [H1, -H2])
      else
        (assert Heq : K t = K s, from
          eq_of_le_of_ge (le_of_not_gt H) (le_of_not_gt J),
        by rewrite [↑K₂, Heq]))

theorem canon_2_bound_left (s t : seq) (Hs : regular s) (n : ℕ+) :
        abs (s n) ≤ rat_of_pnat (K₂ s t) :=
  calc
    abs (s n) ≤ rat_of_pnat (K s) : canon_bound Hs n
    ... ≤ rat_of_pnat (K₂ s t) : rat_of_pnat_le_of_pnat_le (!max_left)

theorem canon_2_bound_right (s t : seq) (Ht : regular t) (n : ℕ+) :
        abs (t n) ≤ rat_of_pnat (K₂ s t) :=
  calc
    abs (t n) ≤ rat_of_pnat (K t) : canon_bound Ht n
    ... ≤ rat_of_pnat (K₂ s t) : rat_of_pnat_le_of_pnat_le (!max_right)

definition sadd (s t : seq) : seq := λ n, (s (2 * n)) + (t (2 * n))

theorem reg_add_reg {s t : seq} (Hs : regular s) (Ht : regular t) : regular (sadd s t) :=
  begin
    rewrite [↑regular at *, ↑sadd],
    intros,
    rewrite add_sub_comm,
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    rewrite add_halves_double,
    apply rat.add_le_add,
    apply Hs,
    apply Ht
  end

definition smul (s t : seq) : seq := λ n : ℕ+, (s ((K₂ s t) * 2 * n)) * (t ((K₂ s t) * 2 * n))

theorem reg_mul_reg {s t : seq} (Hs : regular s) (Ht : regular t) : regular (smul s t) :=
  begin
    rewrite [↑regular at *, ↑smul],
    intros,
    rewrite rewrite_helper,
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    apply rat.le.trans,
    apply rat.add_le_add,
    rewrite abs_mul,
    apply rat.mul_le_mul_of_nonneg_right,
    apply canon_2_bound_left s t Hs,
    apply abs_nonneg,
    rewrite abs_mul,
    apply rat.mul_le_mul_of_nonneg_left,
    apply canon_2_bound_right s t Ht,
    apply abs_nonneg,
    apply ineq_helper,
    apply Ht,
    apply Hs
  end

definition sneg (s : seq) : seq := λ n : ℕ+, - (s n)

theorem reg_neg_reg {s : seq} (Hs : regular s) : regular (sneg s) :=
  begin
    rewrite [↑regular at *, ↑sneg],
    intros,
    rewrite [-abs_neg, neg_sub, sub_neg_eq_add, rat.add.comm],
    apply Hs
  end

-----------------------------------
-- show properties of +, *, -

definition zero : seq := λ n, 0

definition one : seq := λ n, 1

theorem s_add_comm (s t : seq) : sadd s t ≡ sadd t s :=
  begin
    esimp [sadd],
    intro n,
    rewrite [sub_add_eq_sub_sub, rat.add_sub_cancel, rat.sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem s_add_assoc (s t u : seq) (Hs : regular s) (Hu : regular u) :
        sadd (sadd s t) u ≡ sadd s (sadd t u) :=
  begin
    rewrite [↑sadd, ↑equiv, ↑regular at *],
    intros,
    rewrite factor_lemma,
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    apply rat.le.trans,
    rotate 1,
    apply rat.add_le_add_right,
    apply inv_two_mul_le_inv,
    rewrite [-(add_halves (2 * n)), -(add_halves n), factor_lemma_2],
    apply rat.add_le_add,
    apply Hs,
    apply Hu
  end

theorem s_mul_comm (s t : seq) : smul s t ≡ smul t s :=
  begin
    rewrite ↑smul,
    intros n,
    rewrite [*(K₂_symm s t), rat.mul.comm, rat.sub_self, abs_zero],
    apply add_invs_nonneg
  end

definition DK (s t : seq) := (K₂ s t) * 2
theorem DK_rewrite (s t : seq) : (K₂ s t) * 2 = DK s t := rfl

definition TK (s t u : seq) := (DK (λ (n : ℕ+), s (mul (DK s t) n) * t (mul (DK s t) n)) u)

theorem TK_rewrite (s t u : seq) :
        (DK (λ (n : ℕ+), s (mul (DK s t) n) * t (mul (DK s t) n)) u) = TK s t u := rfl

theorem s_mul_assoc_lemma (s t u : seq) (a b c d : ℕ+) :
        abs (s a * t a * u b - s c * t d * u d) ≤ abs (t a) * abs (u b) * abs (s a - s c) +
               abs (s c) * abs (t a) * abs (u b - u d) + abs (s c) * abs (u d) * abs (t a - t d) :=
  begin
    rewrite (rewrite_helper7 _ _ _ _ (s c)),
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    rewrite rat.add.assoc,
    apply rat.add_le_add,
    rewrite 2 abs_mul,
    apply rat.le.refl,
    rewrite [*rat.mul.assoc, -rat.mul_sub_left_distrib, -rat.left_distrib, abs_mul],
    apply rat.mul_le_mul_of_nonneg_left,
    rewrite rewrite_helper,
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    apply rat.add_le_add,
    rewrite abs_mul, apply rat.le.refl,
    rewrite [abs_mul, rat.mul.comm], apply rat.le.refl,
    apply abs_nonneg
  end

definition Kq (s : seq) := rat_of_pnat (K s) + 1
theorem Kq_bound {s : seq} (H : regular s) : ∀ n, abs (s n) ≤ Kq s :=
  begin
    intros,
    apply rat.le_of_lt,
    apply rat.lt_of_le_of_lt,
    apply canon_bound H,
    apply rat.lt_add_of_pos_right,
    apply rat.zero_lt_one
  end

theorem Kq_bound_nonneg {s : seq} (H : regular s) : 0 ≤ Kq s :=
  rat.le.trans !abs_nonneg (Kq_bound H 2)

theorem Kq_bound_pos {s : seq} (H : regular s) : 0 < Kq s :=
  have H1 : 0 ≤ rat_of_pnat (K s), from rat.le.trans (!abs_nonneg) (canon_bound H 2),
  add_pos_of_nonneg_of_pos H1 rat.zero_lt_one

theorem s_mul_assoc_lemma_5 {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
    (a b c : ℕ+) : abs (t a) * abs (u b) * abs (s a - s c) ≤ (Kq t) * (Kq u) * (a⁻¹ + c⁻¹) :=
  begin
    repeat apply rat.mul_le_mul,
    apply Kq_bound Ht,
    apply Kq_bound Hu,
    apply abs_nonneg,
    apply Kq_bound_nonneg Ht,
    apply Hs,
    apply abs_nonneg,
    apply rat.mul_nonneg,
    apply Kq_bound_nonneg Ht,
    apply Kq_bound_nonneg Hu,
  end

theorem s_mul_assoc_lemma_2 {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
  (a b c d : ℕ+) :
     abs (t a) * abs (u b) * abs (s a - s c) + abs (s c) * abs (t a) * abs (u b - u d)
               + abs (s c) * abs (u d) * abs (t a - t d) ≤
    (Kq t) * (Kq u) * (a⁻¹ + c⁻¹) + (Kq s) * (Kq t) * (b⁻¹ + d⁻¹) + (Kq s) * (Kq u) * (a⁻¹ + d⁻¹) :=
  begin
    apply add_le_add_three,
    repeat apply rat.mul_le_mul,
    apply Kq_bound Ht,
    apply Kq_bound Hu,
    apply abs_nonneg,
    apply Kq_bound_nonneg Ht,
    apply Hs,
    apply abs_nonneg,
    apply rat.mul_nonneg,
    apply Kq_bound_nonneg Ht,
    apply Kq_bound_nonneg Hu,
    repeat apply rat.mul_le_mul,
    apply Kq_bound Hs,
    apply Kq_bound Ht,
    apply abs_nonneg,
    apply Kq_bound_nonneg Hs,
    apply Hu,
    apply abs_nonneg,
    apply rat.mul_nonneg,
    apply Kq_bound_nonneg Hs,
    apply Kq_bound_nonneg Ht,
    repeat apply rat.mul_le_mul,
    apply Kq_bound Hs,
    apply Kq_bound Hu,
    apply abs_nonneg,
    apply Kq_bound_nonneg Hs,
    apply Ht,
    apply abs_nonneg,
    apply rat.mul_nonneg,
    apply Kq_bound_nonneg Hs,
    apply Kq_bound_nonneg Hu
  end

theorem s_mul_assoc {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u) :
        smul (smul s t) u ≡ smul s (smul t u) :=
  begin
    apply eq_of_bdd_var,
    repeat apply reg_mul_reg,
    apply Hs,
    apply Ht,
    apply Hu,
    apply reg_mul_reg Hs,
    apply reg_mul_reg Ht Hu,
    intros,
    fapply exists.intro,
    rotate 1,
    intros,
    rewrite [↑smul, *DK_rewrite, *TK_rewrite, -*pnat.mul.assoc, -*rat.mul.assoc],
    apply rat.le.trans,
    apply s_mul_assoc_lemma,
    apply rat.le.trans,
    apply s_mul_assoc_lemma_2,
    apply Hs,
    apply Ht,
    apply Hu,
    rewrite [*s_mul_assoc_lemma_3, -rat.distrib_three_right],
    apply s_mul_assoc_lemma_4,
    apply a,
    repeat apply rat.add_pos,
    repeat apply rat.mul_pos,
    apply Kq_bound_pos Ht,
    apply Kq_bound_pos Hu,
    apply rat.add_pos,
    repeat apply inv_pos,
    repeat apply rat.mul_pos,
    apply Kq_bound_pos Hs,
    apply Kq_bound_pos Ht,
    apply rat.add_pos,
    repeat apply inv_pos,
    repeat apply rat.mul_pos,
    apply Kq_bound_pos Hs,
    apply Kq_bound_pos Hu,
    apply rat.add_pos,
    repeat apply inv_pos,
    apply a_1
  end

theorem zero_is_reg : regular zero :=
  begin
    rewrite [↑regular, ↑zero],
    intros,
    rewrite [rat.sub_zero, abs_zero],
    apply add_invs_nonneg
  end

theorem s_zero_add (s : seq) (H : regular s) : sadd zero s ≡ s :=
  begin
    rewrite [↑sadd, ↑zero, ↑equiv, ↑regular at H],
    intros,
    rewrite [rat.zero_add],
    apply rat.le.trans,
    apply H,
    apply rat.add_le_add,
    apply inv_two_mul_le_inv,
    apply rat.le.refl
  end

theorem s_add_zero (s : seq) (H : regular s) : sadd s zero ≡ s :=
  begin
    rewrite [↑sadd, ↑zero, ↑equiv, ↑regular at H],
    intros,
    rewrite [rat.add_zero],
    apply rat.le.trans,
    apply H,
    apply rat.add_le_add,
    apply inv_two_mul_le_inv,
    apply rat.le.refl
  end

theorem s_neg_cancel (s : seq) (H : regular s) : sadd (sneg s) s ≡ zero :=
  begin
    rewrite [↑sadd, ↑sneg, ↑regular at H, ↑zero, ↑equiv],
    intros,
    rewrite [neg_add_eq_sub, rat.sub_self, rat.sub_zero, abs_zero],
    apply add_invs_nonneg
  end

theorem neg_s_cancel (s : seq) (H : regular s) : sadd s (sneg s) ≡ zero :=
  begin
    apply equiv.trans,
    rotate 3,
    apply s_add_comm,
    apply s_neg_cancel s H,
    apply reg_add_reg,
    apply H,
    apply reg_neg_reg,
    apply H,
    apply reg_add_reg,
    apply reg_neg_reg,
    repeat apply H,
    apply zero_is_reg
  end

theorem add_well_defined {s t u v : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Hv : regular v) (Esu : s ≡ u) (Etv : t ≡ v) : sadd s t ≡ sadd u v :=
  begin
    rewrite [↑sadd, ↑equiv at *],
    intros,
    rewrite [add_sub_comm, add_halves_double],
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    apply rat.add_le_add,
    apply Esu,
    apply Etv
  end

set_option tactic.goal_names false
theorem mul_bound_helper {s t : seq} (Hs : regular s) (Ht : regular t) (a b c : ℕ+) (j : ℕ+) :
        ∃ N : ℕ+, ∀ n : ℕ+, n ≥ N → abs (s (a * n) * t (b * n) - s (c * n) * t (c * n)) ≤ j⁻¹ :=
  begin
    existsi pceil (((rat_of_pnat (K s)) * (b⁻¹ + c⁻¹) + (a⁻¹ + c⁻¹) *
                   (rat_of_pnat (K t))) * (rat_of_pnat j)),
    intros n Hn,
    rewrite rewrite_helper4,
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    apply rat.le.trans,
    rotate 1,
    show n⁻¹ * ((rat_of_pnat (K s)) * (b⁻¹ + c⁻¹)) +
         n⁻¹ * ((a⁻¹ + c⁻¹) * (rat_of_pnat (K t))) ≤ j⁻¹, begin
        rewrite -rat.left_distrib,
        apply rat.le.trans,
        apply rat.mul_le_mul_of_nonneg_right,
        apply pceil_helper Hn,
        repeat (apply rat.mul_pos | apply rat.add_pos | apply inv_pos | apply rat_of_pnat_is_pos),
        apply rat.le_of_lt,
        apply rat.add_pos,
        apply rat.mul_pos,
        apply rat_of_pnat_is_pos,
        apply rat.add_pos,
        repeat apply inv_pos,
        apply rat.mul_pos,
        apply rat.add_pos,
        repeat apply inv_pos,
        apply rat_of_pnat_is_pos,
        have H : (rat_of_pnat (K s) * (b⁻¹ + c⁻¹) + (a⁻¹ + c⁻¹) * rat_of_pnat (K t)) ≠ 0, begin
          apply rat.ne_of_gt,
          repeat (apply rat.mul_pos | apply rat.add_pos | apply rat_of_pnat_is_pos | apply inv_pos),
        end,
        rewrite (rat.div_helper H),
        apply rat.le.refl
    end,
    apply rat.add_le_add,
    rewrite [-rat.mul_sub_left_distrib, abs_mul],
    apply rat.le.trans,
    apply rat.mul_le_mul,
    apply canon_bound,
    apply Hs,
    apply Ht,
    apply abs_nonneg,
    apply rat.le_of_lt,
    apply rat_of_pnat_is_pos,
    rewrite [*inv_mul_eq_mul_inv, -rat.right_distrib, -rat.mul.assoc, rat.mul.comm],
    apply rat.mul_le_mul_of_nonneg_left,
    apply rat.le.refl,
    apply rat.le_of_lt,
    apply inv_pos,
    rewrite [-rat.mul_sub_right_distrib, abs_mul],
    apply rat.le.trans,
    apply rat.mul_le_mul,
    apply Hs,
    apply canon_bound,
    apply Ht,
    apply abs_nonneg,
    apply add_invs_nonneg,
    rewrite [*inv_mul_eq_mul_inv, -rat.right_distrib, mul.comm _ n⁻¹, rat.mul.assoc],
    apply rat.mul_le_mul,
    apply rat.le.refl,
    apply rat.le.refl,
    apply rat.le_of_lt,
    apply rat.mul_pos,
    apply rat.add_pos,
    repeat apply inv_pos,
    apply rat_of_pnat_is_pos,
    apply rat.le_of_lt,
    apply inv_pos
  end

theorem s_distrib {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u) :
                  smul s (sadd t u) ≡ sadd (smul s t) (smul s u) :=
  begin
    apply eq_of_bdd,
    repeat (assumption | apply reg_add_reg | apply reg_mul_reg),
    intros,
    let exh1 := λ a b c, mul_bound_helper Hs Ht a b c (2 * j),
    apply exists.elim,
    apply exh1,
    rotate 3,
    intros N1 HN1,
    let exh2 := λ d e f, mul_bound_helper Hs Hu d e f (2 * j),
    apply exists.elim,
    apply exh2,
    rotate 3,
    intros N2 HN2,
    existsi max N1 N2,
    intros n Hn,
    rewrite [↑sadd at *, ↑smul, rewrite_helper3, -add_halves j, -*pnat.mul.assoc at *],
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    apply rat.add_le_add,
    apply HN1,
    apply le.trans,
    apply max_left N1 N2,
    apply Hn,
    apply HN2,
    apply le.trans,
    apply max_right N1 N2,
    apply Hn
  end

theorem mul_zero_equiv_zero {s t : seq} (Hs : regular s) (Ht : regular t) (Htz : t ≡ zero) :
        smul s t ≡ zero :=
  begin
    apply eq_of_bdd_var,
    apply reg_mul_reg Hs Ht,
    apply zero_is_reg,
    intro ε Hε,
    let Bd := bdd_of_eq_var Ht zero_is_reg Htz (ε / (Kq s))
                            (pos_div_of_pos_of_pos Hε (Kq_bound_pos Hs)),
    apply exists.elim Bd,
    intro N HN,
    existsi N,
    intro n Hn,
    rewrite [↑equiv at Htz, ↑zero at *, rat.sub_zero, ↑smul, abs_mul],
    apply rat.le.trans,
    apply rat.mul_le_mul,
    apply Kq_bound Hs,
    let HN' := λ n, (!rat.sub_zero ▸ HN n),
    apply HN',
    apply le.trans Hn,
    apply pnat.mul_le_mul_left,
    apply abs_nonneg,
    apply rat.le_of_lt (Kq_bound_pos Hs),
    rewrite (rat.mul_div_cancel' (ne.symm (rat.ne_of_lt (Kq_bound_pos Hs)))),
    apply rat.le.refl
  end

theorem neg_bound_eq_bound (s : seq) : K (sneg s) = K s  :=
  by rewrite [↑K, ↑sneg, abs_neg]

theorem neg_bound2_eq_bound2 (s t : seq) : K₂ s (sneg t) = K₂ s t :=
  by rewrite [↑K₂, neg_bound_eq_bound]

theorem sneg_def (s : seq) : (λ (n : ℕ+), -(s n)) = sneg s := rfl

theorem mul_neg_equiv_neg_mul {s t : seq} : smul s (sneg t) ≡ sneg (smul s t) :=
  begin
    rewrite [↑equiv, ↑smul],
    intros,
    rewrite [↑sneg, *sub_neg_eq_add, -neg_mul_eq_mul_neg, rat.add.comm, *sneg_def,
             *neg_bound2_eq_bound2, rat.sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem equiv_of_diff_equiv_zero {s t : seq} (Hs : regular s) (Ht : regular t)
        (H : sadd s (sneg t) ≡ zero) : s ≡ t :=
  begin
    have hsimp : ∀ a b c d e : ℚ, a + b + c + (d + e) = b + d + a + e + c, from
     λ a b c d e, calc
         a + b + c + (d + e) = a + b + (d + e) + c : rat.add.right_comm
                         ... = a + (b + d) + e + c : by rewrite[-*rat.add.assoc]
                         ... = b + d + a + e + c   : rat.add.comm,
    apply eq_of_bdd Hs Ht,
    intros,
    let He := bdd_of_eq H,
    existsi 2 * (2 * (2 * j)),
    intros n Hn,
    rewrite (rewrite_helper5 _ _ (s (2 * n)) (t (2 * n))),
    apply rat.le.trans,
    apply abs_add_three,
    apply rat.le.trans,
    apply add_le_add_three,
    apply Hs,
    rewrite [↑sadd at He, ↑sneg at He, ↑zero at He],
    let He' := λ a b c, !rat.sub_zero ▸ (He a b c),
    apply (He' _ _ Hn),
    apply Ht,
    rewrite [hsimp, add_halves, -(add_halves j), -(add_halves (2 * j)), -*rat.add.assoc],
    apply rat.add_le_add_right,
    apply add_le_add_three,
    repeat (apply rat.le.trans; apply inv_ge_of_le Hn; apply inv_two_mul_le_inv)
  end

theorem s_sub_cancel (s : seq) : sadd s (sneg s) ≡ zero :=
  begin
    rewrite [↑equiv, ↑sadd, ↑sneg, ↑zero],
    intros,
    rewrite [rat.sub_zero, rat.sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem diff_equiv_zero_of_equiv {s t : seq} (Hs : regular s) (Ht : regular t) (H : s ≡ t) :
        sadd s (sneg t) ≡ zero :=
  begin
    let Hnt := reg_neg_reg Ht,
    let Hsnt := reg_add_reg Hs Hnt,
    let Htnt := reg_add_reg Ht Hnt,
    apply equiv.trans,
    rotate 4,
    apply s_sub_cancel t,
    rotate 2,
    apply zero_is_reg,
    apply add_well_defined,
    repeat assumption,
    apply equiv.refl,
    repeat assumption
  end

theorem mul_well_defined_half1 {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Etu : t ≡ u) : smul s t ≡ smul s u :=
  begin
    apply equiv_of_diff_equiv_zero,
    rotate 2,
    apply equiv.trans,
    rotate 3,
    apply equiv.symm,
    apply add_well_defined,
    rotate 4,
    apply equiv.refl,
    apply mul_neg_equiv_neg_mul,
    apply equiv.trans,
    rotate 3,
    apply equiv.symm,
    apply s_distrib,
    rotate 3,
    apply mul_zero_equiv_zero,
    rotate 2,
    apply diff_equiv_zero_of_equiv,
    repeat (assumption | apply reg_mul_reg | apply reg_neg_reg | apply reg_add_reg |
            apply zero_is_reg)
  end

theorem mul_well_defined_half2 {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Est : s ≡ t) : smul s u ≡ smul t u :=
  begin
    apply equiv.trans,
    rotate 3,
    apply s_mul_comm,
    apply equiv.trans,
    rotate 3,
    apply mul_well_defined_half1,
    rotate 2,
    apply Ht,
    rotate 1,
    apply s_mul_comm,
    repeat (assumption | apply reg_mul_reg)
end

theorem mul_well_defined {s t u v : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Hv : regular v) (Esu : s ≡ u) (Etv : t ≡ v) : smul s t ≡ smul u v :=
  begin
    apply equiv.trans,
    exact reg_mul_reg Hs Ht,
    exact reg_mul_reg Hs Hv,
    exact reg_mul_reg Hu Hv,
    apply mul_well_defined_half1,
    repeat assumption,
    apply mul_well_defined_half2,
    repeat assumption
  end

theorem neg_well_defined {s t : seq} (Est : s ≡ t) : sneg s ≡ sneg t :=
  begin
    rewrite [↑sneg, ↑equiv at *],
    intros,
    rewrite [-abs_neg, neg_sub, sub_neg_eq_add, rat.add.comm],
    apply Est
  end

theorem one_is_reg : regular one :=
  begin
    rewrite [↑regular, ↑one],
    intros,
    rewrite [rat.sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem s_one_mul {s : seq} (H : regular s) : smul one s ≡ s :=
  begin
    rewrite ↑equiv,
    intros,
    rewrite [↑smul, ↑one, rat.one_mul],
    apply rat.le.trans,
    apply H,
    apply rat.add_le_add_right,
    apply inv_mul_le_inv
  end

theorem s_mul_one {s : seq} (H : regular s) : smul s one ≡ s :=
  begin
    apply equiv.trans,
    apply reg_mul_reg H one_is_reg,
    rotate 2,
    apply s_mul_comm,
    apply s_one_mul H,
    apply reg_mul_reg one_is_reg H,
    apply H
  end

theorem zero_nequiv_one : ¬ zero ≡ one :=
  begin
    intro Hz,
    rewrite [↑equiv at Hz, ↑zero at Hz, ↑one at Hz],
    let H := Hz (2 * 2),
    rewrite [rat.zero_sub at H, abs_neg at H, add_halves at H],
    have H' : pone⁻¹ ≤ 2⁻¹, from calc
      pone⁻¹ = 1 : by rewrite -pone_inv
      ... = abs 1 : abs_of_pos zero_lt_one
      ... ≤ 2⁻¹ : H,
    let H'' := ge_of_inv_le H',
    apply absurd (one_lt_two) (not_lt_of_ge H'')
  end

---------------------------------------------
-- constant sequences

definition const (a : ℚ) : seq := λ n, a

theorem const_reg (a : ℚ) : regular (const a) :=
  begin
    intros,
    rewrite [↑const, rat.sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem add_consts (a b : ℚ) : sadd (const a) (const b) ≡ const (a + b) :=
  begin
    rewrite [↑sadd, ↑const],
    apply equiv.refl
  end

---------------------------------------------
-- create the type of regular sequences and lift theorems

record reg_seq : Type :=
  (sq : seq) (is_reg : regular sq)

definition requiv (s t : reg_seq) := (reg_seq.sq s) ≡ (reg_seq.sq t)
definition requiv.refl (s : reg_seq) : requiv s s := equiv.refl (reg_seq.sq s)
definition requiv.symm (s t : reg_seq) (H : requiv s t) : requiv t s :=
  equiv.symm (reg_seq.sq s) (reg_seq.sq t) H
definition requiv.trans (s t u : reg_seq) (H : requiv s t) (H2 : requiv t u) : requiv s u :=
  equiv.trans _ _ _ (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u) H H2

definition radd (s t : reg_seq) : reg_seq :=
  reg_seq.mk (sadd (reg_seq.sq s) (reg_seq.sq t))
             (reg_add_reg (reg_seq.is_reg s) (reg_seq.is_reg t))
infix `+` := radd

definition rmul (s t : reg_seq) : reg_seq :=
  reg_seq.mk (smul (reg_seq.sq s) (reg_seq.sq t))
             (reg_mul_reg (reg_seq.is_reg s) (reg_seq.is_reg t))
infix `*` := rmul

definition rneg (s : reg_seq) : reg_seq :=
  reg_seq.mk (sneg (reg_seq.sq s)) (reg_neg_reg (reg_seq.is_reg s))
prefix `-` := rneg

definition radd_well_defined {s t u v : reg_seq} (H : requiv s u) (H2 : requiv t v) :
           requiv (s + t) (u + v) :=
  add_well_defined (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u) (reg_seq.is_reg v) H H2

definition rmul_well_defined {s t u v : reg_seq} (H : requiv s u) (H2 : requiv t v) :
           requiv (s * t) (u * v) :=
  mul_well_defined (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u) (reg_seq.is_reg v) H H2

definition rneg_well_defined {s t : reg_seq} (H : requiv s t) : requiv (-s) (-t) :=
  neg_well_defined H

theorem requiv_is_equiv : equivalence requiv :=
  mk_equivalence requiv requiv.refl requiv.symm requiv.trans

definition reg_seq.to_setoid [instance] : setoid reg_seq :=
  ⦃setoid, r := requiv, iseqv := requiv_is_equiv⦄

definition r_zero : reg_seq :=
  reg_seq.mk (zero) (zero_is_reg)

definition r_one : reg_seq :=
  reg_seq.mk (one) (one_is_reg)

theorem r_add_comm (s t : reg_seq) :  requiv (s + t) (t + s) :=
  s_add_comm (reg_seq.sq s) (reg_seq.sq t)

theorem r_add_assoc (s t u : reg_seq) : requiv (s + t + u) (s + (t + u)) :=
  s_add_assoc (reg_seq.sq s) (reg_seq.sq t) (reg_seq.sq u) (reg_seq.is_reg s) (reg_seq.is_reg u)

theorem r_zero_add (s : reg_seq) : requiv (r_zero + s) s :=
  s_zero_add (reg_seq.sq s) (reg_seq.is_reg s)

theorem r_add_zero (s : reg_seq) : requiv (s + r_zero) s :=
  s_add_zero (reg_seq.sq s) (reg_seq.is_reg s)

theorem r_neg_cancel (s : reg_seq) : requiv (-s + s) r_zero :=
  s_neg_cancel (reg_seq.sq s) (reg_seq.is_reg s)

theorem r_mul_comm (s t : reg_seq) : requiv (s * t) (t * s) :=
  s_mul_comm (reg_seq.sq s) (reg_seq.sq t)

theorem r_mul_assoc (s t u : reg_seq) : requiv (s * t * u) (s * (t * u)) :=
  s_mul_assoc (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u)

theorem r_mul_one (s : reg_seq) : requiv (s * r_one) s :=
  s_mul_one (reg_seq.is_reg s)

theorem r_one_mul (s : reg_seq) : requiv (r_one * s) s :=
  s_one_mul (reg_seq.is_reg s)

theorem r_distrib (s t u : reg_seq) : requiv (s * (t + u)) (s * t + s * u) :=
  s_distrib (reg_seq.is_reg s) (reg_seq.is_reg t) (reg_seq.is_reg u)

theorem r_zero_nequiv_one : ¬ requiv r_zero r_one :=
  zero_nequiv_one

definition r_const (a : ℚ) : reg_seq := reg_seq.mk (const a) (const_reg a)

theorem r_add_consts (a b : ℚ) : requiv (r_const a + r_const b) (r_const (a + b)) := add_consts a b

end s
----------------------------------------------
-- take quotients to get ℝ and show it's a comm ring

open s
definition real := quot reg_seq.to_setoid
namespace real
notation `ℝ` := real

definition add (x y : ℝ) : ℝ :=
  (quot.lift_on₂ x y (λ a b, quot.mk (a + b))
                     (take a b c d : reg_seq, take Hab : requiv a c, take Hcd : requiv b d,
                       quot.sound (radd_well_defined Hab Hcd)))
protected definition prio := num.pred rat.prio
infix [priority real.prio] `+` := add

definition mul (x y : ℝ) : ℝ :=
  (quot.lift_on₂ x y (λ a b, quot.mk (a * b))
                     (take a b c d : reg_seq, take Hab : requiv a c, take Hcd : requiv b d,
                       quot.sound (rmul_well_defined Hab Hcd)))
infix [priority real.prio] `*` := mul

definition neg (x : ℝ) : ℝ :=
  (quot.lift_on x (λ a, quot.mk (-a)) (take a b : reg_seq, take Hab : requiv a b,
                                   quot.sound (rneg_well_defined Hab)))
prefix [priority real.prio] `-` := neg

definition zero : ℝ := quot.mk r_zero
--notation 0 := zero

definition one : ℝ := quot.mk r_one

theorem add_comm (x y : ℝ) : x + y = y + x :=
  quot.induction_on₂ x y (λ s t, quot.sound (r_add_comm s t))

theorem add_assoc (x y z : ℝ) : x + y + z = x + (y + z) :=
  quot.induction_on₃ x y z (λ s t u, quot.sound (r_add_assoc s t u))

theorem zero_add (x : ℝ) : zero + x = x :=
  quot.induction_on x (λ s, quot.sound (r_zero_add s))

theorem add_zero (x : ℝ) : x + zero = x :=
  quot.induction_on x (λ s, quot.sound (r_add_zero s))

theorem neg_cancel (x : ℝ) : -x + x = zero :=
  quot.induction_on x (λ s, quot.sound (r_neg_cancel s))

theorem mul_assoc (x y z : ℝ) : x * y * z = x * (y * z) :=
  quot.induction_on₃ x y z (λ s t u, quot.sound (r_mul_assoc s t u))

theorem mul_comm (x y : ℝ) : x * y = y * x :=
  quot.induction_on₂ x y (λ s t, quot.sound (r_mul_comm s t))

theorem one_mul (x : ℝ) : one * x = x :=
  quot.induction_on x (λ s, quot.sound (r_one_mul s))

theorem mul_one (x : ℝ) : x * one = x :=
  quot.induction_on x (λ s, quot.sound (r_mul_one s))

theorem distrib (x y z : ℝ) : x * (y + z) = x * y + x * z :=
  quot.induction_on₃ x y z (λ s t u, quot.sound (r_distrib s t u))

theorem distrib_l (x y z : ℝ) : (x + y) * z = x * z + y * z :=
  by rewrite [mul_comm, distrib, {x * _}mul_comm, {y * _}mul_comm] -- this shouldn't be necessary

theorem zero_ne_one : ¬ zero = one :=
  take H : zero = one,
  absurd (quot.exact H) (r_zero_nequiv_one)

protected definition comm_ring [reducible] : algebra.comm_ring ℝ :=
  begin
    fapply algebra.comm_ring.mk,
    exact add,
    exact add_assoc,
    exact zero,
    exact zero_add,
    exact add_zero,
    exact neg,
    exact neg_cancel,
    exact add_comm,
    exact mul,
    exact mul_assoc,
    apply one,
    apply one_mul,
    apply mul_one,
    apply distrib,
    apply distrib_l,
    apply mul_comm
  end

definition const (a : ℚ) : ℝ := quot.mk (s.r_const a)

theorem add_consts (a b : ℚ) : const a + const b = const (a + b) :=
  quot.sound (s.r_add_consts a b)

theorem sub_consts (a b : ℚ) : const a + -const b = const (a - b) := !add_consts

theorem add_half_const (n : ℕ+) : const (2 * n)⁻¹ + const (2 * n)⁻¹ = const (n⁻¹) :=
  by rewrite [add_consts, pnat.add_halves]

end real
