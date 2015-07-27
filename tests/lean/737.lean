/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
The real numbers, constructed as equivalence classes of Cauchy sequences of rationals.
This construction follows Bishop and Bridges (1985).

To do:
 o Break positive naturals into their own file and fill in sorry's
 o Fill in sorrys for helper lemmas that will not be handled by simplifier
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

-- this can move to pnat once sorry is filled in
theorem find_midpoint {a b : ℚ} (H : a > b) : ∃ c : ℚ, a > b + c ∧ c > 0 :=
sorry
theorem add_sub_comm (a b c d : ℚ) : a + b - (c + d) = (a - c) + (b - d) :=
sorry

theorem s_mul_assoc_lemma_4 {n : ℕ+} {ε q : ℚ} (Hε : ε > 0) (Hq : q > 0) (H : n ≥ pceil (q / ε)) :
        q * n⁻¹ ≤ ε :=
sorry
theorem s_mul_assoc_lemma_3 (a b n : ℕ+) (p : ℚ) :
        p * ((a * n)⁻¹ + (b * n)⁻¹) = p * (a⁻¹ + b⁻¹) * n⁻¹ :=
sorry

theorem find_thirds (a b : ℚ) : ∃ n : ℕ+, a + n⁻¹ + n⁻¹ + n⁻¹ < a + b := sorry

theorem squeeze {a b : ℚ} (H : ∀ j : ℕ+, a ≤ b + j⁻¹ + j⁻¹ + j⁻¹) : a ≤ b :=
sorry

theorem squeeze_2 {a b : ℚ} (H : ∀ ε : ℚ, ε > 0 → a ≥ b - ε) : a ≥ b :=
sorry

theorem rewrite_helper (a b c d : ℚ) : a * b  - c * d = a * (b - d) + (a - c) * d :=
sorry

theorem rewrite_helper3 (a b c d e f g: ℚ) : a * (b + c) - (d * e + f * g) =
        (a * b - d * e) + (a * c - f * g) :=
sorry

theorem rewrite_helper4 (a b c d : ℚ) : a * b - c * d = (a * b - a * d) + (a * d - c * d) := sorry

theorem rewrite_helper5 (a b x y : ℚ) : a - b = (a - x) + (x - y) + (y - b) := sorry

theorem rewrite_helper7 (a b c d x : ℚ) :
        a * b * c - d = (b * c) * (a - x) + (x * b * c - d) := sorry

theorem ineq_helper (a b : ℚ) (k m n : ℕ+) (H : a ≤ (k * 2 * m)⁻¹ + (k * 2 * n)⁻¹)
                    (H2 : b ≤ (k * 2 * m)⁻¹ + (k * 2 * n)⁻¹) :
        (rat_of_pnat k) * a + b * (rat_of_pnat k) ≤ m⁻¹ + n⁻¹ := sorry

theorem factor_lemma (a b c d e : ℚ) : abs (a + b + c - (d + (b + e))) = abs ((a - d) + (c - e)) :=
  sorry

theorem factor_lemma_2 (a b c d : ℚ) : (a + b) + (c + d) = (a + c) + (d + b) := sorry

namespace s

notation `seq` := ℕ+ → ℚ

definition regular (s : seq) := ∀ m n : ℕ+, abs (s m - s n) ≤ m⁻¹ + n⁻¹

definition equiv (s t : seq) := ∀ n : ℕ+, abs (s n - t n) ≤ n⁻¹ + n⁻¹
infix `≡` := equiv

theorem equiv.refl (s : seq) : s ≡ s :=
sorry

theorem equiv.symm (s t : seq) (H : s ≡ t) : t ≡ s :=
sorry

theorem bdd_of_eq {s t : seq} (H : s ≡ t) :
        ∀ j : ℕ+, ∀ n : ℕ+, n ≥ 2 * j → abs (s n - t n) ≤ j⁻¹ :=
sorry

theorem eq_of_bdd {s t : seq} (Hs : regular s) (Ht : regular t)
        (H : ∀ j : ℕ+, ∃ Nj : ℕ+, ∀ n : ℕ+, Nj ≤ n → abs (s n - t n) ≤ j⁻¹) : s ≡ t :=
sorry

theorem eq_of_bdd_var {s t : seq} (Hs : regular s) (Ht : regular t)
        (H : ∀ ε : ℚ, ε > 0 → ∃ Nj : ℕ+, ∀ n : ℕ+, Nj ≤ n → abs (s n - t n) ≤ ε) : s ≡ t :=
sorry

set_option pp.beta false
theorem pnat_bound {ε : ℚ} (Hε : ε > 0) : ∃ p : ℕ+, p⁻¹ ≤ ε :=
sorry

theorem bdd_of_eq_var {s t : seq} (Hs : regular s) (Ht : regular t) (Heq : s ≡ t) :
        ∀ ε : ℚ, ε > 0 → ∃ Nj : ℕ+, ∀ n : ℕ+, Nj ≤ n → abs (s n - t n) ≤ ε :=
sorry

theorem equiv.trans (s t u : seq) (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (H : s ≡ t) (H2 : t ≡ u) : s ≡ u :=
sorry

-----------------------------------
-- define operations on cauchy sequences. show operations preserve regularity

definition K (s : seq) : ℕ+ := pnat.pos (ubound (abs (s pone)) + 1 + 1) dec_trivial

theorem canon_bound {s : seq} (Hs : regular s) (n : ℕ+) : abs (s n) ≤ rat_of_pnat (K s) :=
sorry

definition K₂ (s t : seq) := max (K s) (K t)

theorem K₂_symm (s t : seq) : K₂ s t = K₂ t s :=
sorry

theorem canon_2_bound_left (s t : seq) (Hs : regular s) (n : ℕ+) :
        abs (s n) ≤ rat_of_pnat (K₂ s t) :=
sorry

theorem canon_2_bound_right (s t : seq) (Ht : regular t) (n : ℕ+) :
        abs (t n) ≤ rat_of_pnat (K₂ s t) :=
sorry

definition sadd (s t : seq) : seq := λ n, (s (2 * n)) + (t (2 * n))

theorem reg_add_reg {s t : seq} (Hs : regular s) (Ht : regular t) : regular (sadd s t) :=
sorry

definition smul (s t : seq) : seq := λ n : ℕ+, (s ((K₂ s t) * 2 * n)) * (t ((K₂ s t) * 2 * n))

theorem reg_mul_reg {s t : seq} (Hs : regular s) (Ht : regular t) : regular (smul s t) :=
sorry

definition sneg (s : seq) : seq := λ n : ℕ+, - (s n)

theorem reg_neg_reg {s : seq} (Hs : regular s) : regular (sneg s) :=
sorry
-----------------------------------
-- show properties of +, *, -

definition zero : seq := λ n, 0

definition one : seq := λ n, 1

theorem s_add_comm (s t : seq) : sadd s t ≡ sadd t s :=
sorry

theorem s_add_assoc (s t u : seq) (Hs : regular s) (Hu : regular u) :
        sadd (sadd s t) u ≡ sadd s (sadd t u) :=
sorry

theorem s_mul_comm (s t : seq) : smul s t ≡ smul t s :=
sorry

definition DK (s t : seq) := (K₂ s t) * 2
theorem DK_rewrite (s t : seq) : (K₂ s t) * 2 = DK s t := rfl

definition TK (s t u : seq) := (DK (λ (n : ℕ+), s (mul (DK s t) n) * t (mul (DK s t) n)) u)

theorem TK_rewrite (s t u : seq) :
        (DK (λ (n : ℕ+), s (mul (DK s t) n) * t (mul (DK s t) n)) u) = TK s t u := rfl

theorem s_mul_assoc_lemma (s t u : seq) (a b c d : ℕ+) :
        abs (s a * t a * u b - s c * t d * u d) ≤ abs (t a) * abs (u b) * abs (s a - s c) +
               abs (s c) * abs (t a) * abs (u b - u d) + abs (s c) * abs (u d) * abs (t a - t d) :=
sorry

definition Kq (s : seq) := rat_of_pnat (K s) + 1

theorem Kq_bound {s : seq} (H : regular s) : ∀ n, abs (s n) ≤ Kq s :=
sorry

theorem Kq_bound_nonneg {s : seq} (H : regular s) : 0 ≤ Kq s :=
  rat.le.trans !abs_nonneg (Kq_bound H 2)

theorem Kq_bound_pos {s : seq} (H : regular s) : 0 < Kq s :=
sorry

theorem s_mul_assoc_lemma_5 {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
    (a b c : ℕ+) : abs (t a) * abs (u b) * abs (s a - s c) ≤ (Kq t) * (Kq u) * (a⁻¹ + c⁻¹) :=
sorry

theorem s_mul_assoc_lemma_2 {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
  (a b c d : ℕ+) :
     abs (t a) * abs (u b) * abs (s a - s c) + abs (s c) * abs (t a) * abs (u b - u d)
               + abs (s c) * abs (u d) * abs (t a - t d) ≤
    (Kq t) * (Kq u) * (a⁻¹ + c⁻¹) + (Kq s) * (Kq t) * (b⁻¹ + d⁻¹) + (Kq s) * (Kq u) * (a⁻¹ + d⁻¹) :=
sorry

theorem s_mul_assoc {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u) :
        smul (smul s t) u ≡ smul s (smul t u) :=
sorry

theorem zero_is_reg : regular zero :=
sorry

theorem s_zero_add (s : seq) (H : regular s) : sadd zero s ≡ s :=
sorry

theorem s_add_zero (s : seq) (H : regular s) : sadd s zero ≡ s :=
sorry

theorem s_neg_cancel (s : seq) (H : regular s) : sadd (sneg s) s ≡ zero :=
sorry

theorem neg_s_cancel (s : seq) (H : regular s) : sadd s (sneg s) ≡ zero :=
sorry

theorem add_well_defined {s t u v : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (Hv : regular v) (Esu : s ≡ u) (Etv : t ≡ v) : sadd s t ≡ sadd u v :=
sorry

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
     end
end
end s
