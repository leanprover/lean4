/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
The real numbers, constructed as equivalence classes of Cauchy sequences of rationals.
This construction follows Bishop and Bridges (1985).

The construction of the reals is arranged in four files.

- basic.lean proves properties about regular sequences of rationals in the namespace rat_seq,
  defines ℝ to be the quotient type of regular sequences mod equivalence, and shows ℝ is a ring
  in namespace real. No classical axioms are used.

- order.lean defines an order on regular sequences and lifts the order to ℝ. In the namespace real,
  ℝ is shown to be an ordered ring. No classical axioms are used.

- division.lean defines the inverse of a regular sequence and lifts this to ℝ. If a sequence is
  equivalent to the 0 sequence, its inverse is the zero sequence. In the namespace real, ℝ is shown
  to be an ordered field. This construction is classical.

- complete.lean
-/
import data.nat data.rat.order data.pnat
open nat eq pnat
open algebra
open - [coercions] rat

local postfix `⁻¹` := pnat.inv

-- small helper lemmas

private theorem s_mul_assoc_lemma_3 (a b n : ℕ+) (p : ℚ) :
        p * ((a * n)⁻¹ + (b * n)⁻¹) = p * (a⁻¹ + b⁻¹) * n⁻¹ :=
by rewrite [rat.mul.assoc, right_distrib, *inv_mul_eq_mul_inv]

private theorem s_mul_assoc_lemma_4 {n : ℕ+} {ε q : ℚ} (Hε : ε > 0) (Hq : q > 0) (H : n ≥ pceil (q / ε)) :
        q * n⁻¹ ≤ ε :=
begin
  let H2 := pceil_helper H (div_pos_of_pos_of_pos Hq Hε),
  let H3 := mul_le_of_le_div (div_pos_of_pos_of_pos Hq Hε) H2,
  rewrite -(one_mul ε),
  apply mul_le_mul_of_mul_div_le,
  repeat assumption
end

private theorem find_thirds (a b : ℚ) (H : b > 0) : ∃ n : ℕ+, a + n⁻¹ + n⁻¹ + n⁻¹ < a + b :=
let n := pceil (of_nat 4 / b) in
have of_nat 3 * n⁻¹ < b, from calc
   of_nat 3 * n⁻¹ < of_nat 4 * n⁻¹
                  : mul_lt_mul_of_pos_right dec_trivial !inv_pos
              ... ≤ of_nat 4 * (b / of_nat 4)
                  : mul_le_mul_of_nonneg_left (!inv_pceil_div dec_trivial H) !of_nat_nonneg
              ... = b / of_nat 4 * of_nat 4 : algebra.mul.comm
              ... = b : !div_mul_cancel dec_trivial,
  exists.intro n (calc
    a + n⁻¹ + n⁻¹ + n⁻¹ = a + (1 + 1 + 1) * n⁻¹ : by rewrite [+right_distrib, +rat.one_mul, -+algebra.add.assoc]
                    ... = a + of_nat 3 * n⁻¹    : {show 1+1+1=of_nat 3, from dec_trivial}
                    ... < a + b                 : rat.add_lt_add_left this a)


private theorem squeeze {a b : ℚ} (H : ∀ j : ℕ+, a ≤ b + j⁻¹ + j⁻¹ + j⁻¹) : a ≤ b :=
begin
  apply algebra.le_of_not_gt,
  intro Hb,
  cases exists_add_lt_and_pos_of_lt Hb with [c, Hc],
  cases find_thirds b c (and.right Hc) with [j, Hbj],
  have Ha : a > b + j⁻¹ + j⁻¹ + j⁻¹, from lt.trans Hbj (and.left Hc),
  apply (not_le_of_gt Ha) !H
end

private theorem rewrite_helper (a b c d : ℚ) : a * b  - c * d = a * (b - d) + (a - c) * d :=
by rewrite [algebra.mul_sub_left_distrib, algebra.mul_sub_right_distrib, add_sub, algebra.sub_add_cancel]

private theorem rewrite_helper3 (a b c d e f g: ℚ) : a * (b + c) - (d * e + f * g) =
        (a * b - d * e) + (a * c - f * g) :=
by rewrite [rat.mul.left_distrib, add_sub_comm]

private theorem rewrite_helper4 (a b c d : ℚ) : a * b - c * d = (a * b - a * d) + (a * d - c * d) :=
by rewrite[add_sub, algebra.sub_add_cancel]

private theorem rewrite_helper5 (a b x y : ℚ) : a - b = (a - x) + (x - y) + (y - b) :=
by rewrite[*add_sub, *algebra.sub_add_cancel]

private theorem rewrite_helper7 (a b c d x : ℚ) :
        a * b * c - d = (b * c) * (a - x) + (x * b * c - d) :=
begin
  have ∀ (a b c : ℚ), a * b * c = b * c * a,
    begin
      intros a b c,
      rewrite (algebra.mul.right_comm b c a),
      rewrite (algebra.mul.comm b a)
    end,
  rewrite[algebra.mul_sub_left_distrib, add_sub],
  calc
     a * b * c - d = a * b * c - x * b * c + x * b * c - d : algebra.sub_add_cancel
               ... = b * c * a - b * c * x + x * b * c - d :
       begin
         rewrite [this a b c, this x b c]
       end
end

private theorem ineq_helper (a b : ℚ) (k m n : ℕ+) (H : a ≤ (k * 2 * m)⁻¹ + (k * 2 * n)⁻¹)
                    (H2 : b ≤ (k * 2 * m)⁻¹ + (k * 2 * n)⁻¹) :
        (rat_of_pnat k) * a + b * (rat_of_pnat k) ≤ m⁻¹ + n⁻¹ :=
assert H3 : (k * 2 * m)⁻¹ + (k * 2 * n)⁻¹ = (2 * k)⁻¹ * (m⁻¹ + n⁻¹),
  begin
    rewrite [rat.mul.left_distrib,*inv_mul_eq_mul_inv],
    rewrite (rat.mul.comm k⁻¹)
  end,
have H' : a ≤ (2 * k)⁻¹ * (m⁻¹ + n⁻¹),
  begin
    rewrite H3 at H,
    exact H
  end,
have H2' : b ≤ (2 * k)⁻¹ * (m⁻¹ + n⁻¹),
  begin
    rewrite H3 at H2,
    exact H2
  end,
have a + b ≤ k⁻¹ * (m⁻¹ + n⁻¹), from calc
   a + b ≤ (2 * k)⁻¹ * (m⁻¹ + n⁻¹) + (2 * k)⁻¹ * (m⁻¹ + n⁻¹) : algebra.add_le_add H' H2'
     ... = ((2 * k)⁻¹ + (2 * k)⁻¹) * (m⁻¹ + n⁻¹)             : by rewrite rat.mul.right_distrib
     ... = k⁻¹ * (m⁻¹ + n⁻¹)                                 : by rewrite (pnat.add_halves k),
calc (rat_of_pnat k) * a + b * (rat_of_pnat k)
         = (rat_of_pnat k) * a + (rat_of_pnat k) * b         : by rewrite (algebra.mul.comm b)
     ... = (rat_of_pnat k) * (a + b)                         : algebra.left_distrib
     ... ≤ (rat_of_pnat k) * (k⁻¹ * (m⁻¹ + n⁻¹))             :
             iff.mp (!algebra.le_iff_mul_le_mul_left !rat_of_pnat_is_pos) this
     ... = m⁻¹ + n⁻¹                                         :
             by rewrite[-rat.mul.assoc, inv_cancel_left, rat.one_mul]

private theorem factor_lemma (a b c d e : ℚ) : abs (a + b + c - (d + (b + e))) = abs ((a - d) + (c - e)) :=
  !congr_arg (calc
    a + b + c - (d + (b + e)) = a + b + c - (d + b + e)   : rat.add.assoc
                         ...  = a + b - (d + b) + (c - e) : add_sub_comm
                         ...  = a + b - b - d + (c - e)   : sub_add_eq_sub_sub_swap
                         ...  = a - d + (c - e)           : algebra.add_sub_cancel)

private theorem factor_lemma_2 (a b c d : ℚ) : (a + b) + (c + d) = (a + c) + (d + b) :=
begin
   let H := (binary.comm4 rat.add.comm rat.add.assoc a b c d),
   rewrite [algebra.add.comm b d at H],
   exact H
end

--------------------------------------
-- define cauchy sequences and equivalence. show equivalence actually is one
namespace rat_seq

notation `seq` := ℕ+ → ℚ

definition regular (s : seq) := ∀ m n : ℕ+, abs (s m - s n) ≤ m⁻¹ + n⁻¹

definition equiv (s t : seq) := ∀ n : ℕ+, abs (s n - t n) ≤ n⁻¹ + n⁻¹
infix `≡` := equiv

theorem equiv.refl (s : seq) : s ≡ s :=
begin
  intros,
  rewrite [algebra.sub_self, abs_zero],
  apply add_invs_nonneg
end

theorem equiv.symm (s t : seq) (H : s ≡ t) : t ≡ s :=
begin
  intros,
  rewrite [-abs_neg, neg_sub],
  exact H n
end

theorem bdd_of_eq {s t : seq} (H : s ≡ t) :
        ∀ j : ℕ+, ∀ n : ℕ+, n ≥ 2 * j → abs (s n - t n) ≤ j⁻¹ :=
begin
  intros [j, n, Hn],
  apply algebra.le.trans,
  apply H,
  rewrite -(add_halves j),
  apply algebra.add_le_add,
  apply inv_ge_of_le Hn,
  apply inv_ge_of_le Hn
end

theorem eq_of_bdd {s t : seq} (Hs : regular s) (Ht : regular t)
        (H : ∀ j : ℕ+, ∃ Nj : ℕ+, ∀ n : ℕ+, Nj ≤ n → abs (s n - t n) ≤ j⁻¹) : s ≡ t :=
  begin
    intros,
    have Hj : (∀ j : ℕ+, abs (s n - t n) ≤ n⁻¹ + n⁻¹ + j⁻¹ + j⁻¹ + j⁻¹), begin
      intros,
      cases H j with [Nj, HNj],
      rewrite [-(sub_add_cancel (s n) (s (max j Nj))), +sub_eq_add_neg, algebra.add.assoc (s n + -s (max j Nj)),
              ↑regular at *],
      apply rat.le.trans,
      apply abs_add_le_abs_add_abs,
      apply rat.le.trans,
      apply add_le_add,
      apply Hs,
      rewrite [-(sub_add_cancel (s (max j Nj)) (t (max j Nj))), rat.add.assoc],
      apply abs_add_le_abs_add_abs,
      apply rat.le.trans,
      apply rat.add_le_add_left,
      apply add_le_add,
      apply HNj (max j Nj) (max_right j Nj),
      apply Ht,
      have hsimp : ∀ m : ℕ+, n⁻¹ + m⁻¹ + (j⁻¹ + (m⁻¹ + n⁻¹)) = n⁻¹ + n⁻¹ + j⁻¹ + (m⁻¹ + m⁻¹),
        from λm, calc
           n⁻¹ + m⁻¹ + (j⁻¹ + (m⁻¹ + n⁻¹)) = n⁻¹ + (j⁻¹ + (m⁻¹ + n⁻¹)) + m⁻¹ : algebra.add.right_comm
                                       ... = n⁻¹ + (j⁻¹ + m⁻¹ + n⁻¹) + m⁻¹   : rat.add.assoc
                                       ... = n⁻¹ + (n⁻¹ + (j⁻¹ + m⁻¹)) + m⁻¹ : rat.add.comm
                                       ... = n⁻¹ + n⁻¹ + j⁻¹ + (m⁻¹ + m⁻¹)   : by rewrite[-*rat.add.assoc],
      rewrite hsimp,
      have Hms : (max j Nj)⁻¹ + (max j Nj)⁻¹ ≤ j⁻¹ + j⁻¹, begin
        apply add_le_add,
        apply inv_ge_of_le (max_left j Nj),
        apply inv_ge_of_le (max_left j Nj),
      end,
     apply (calc
       n⁻¹ + n⁻¹ + j⁻¹ + ((max j Nj)⁻¹ + (max j Nj)⁻¹) ≤ n⁻¹ + n⁻¹ + j⁻¹ + (j⁻¹ + j⁻¹) :
         rat.add_le_add_left Hms
       ... = n⁻¹ + n⁻¹ + j⁻¹ + j⁻¹ + j⁻¹ : by rewrite *rat.add.assoc)
    end,
    apply squeeze Hj
  end

theorem eq_of_bdd_var {s t : seq} (Hs : regular s) (Ht : regular t)
        (H : ∀ ε : ℚ, ε > 0 → ∃ Nj : ℕ+, ∀ n : ℕ+, Nj ≤ n → abs (s n - t n) ≤ ε) : s ≡ t :=
  begin
    apply eq_of_bdd,
    repeat assumption,
    intros,
    apply H,
    apply inv_pos
  end

theorem bdd_of_eq_var {s t : seq} (Hs : regular s) (Ht : regular t) (Heq : s ≡ t) :
        ∀ ε : ℚ, ε > 0 → ∃ Nj : ℕ+, ∀ n : ℕ+, Nj ≤ n → abs (s n - t n) ≤ ε :=
  begin
    intro ε Hε,
    cases pnat_bound Hε with [N, HN],
    existsi 2 * N,
    intro n Hn,
    apply rat.le.trans,
    apply bdd_of_eq Heq N n Hn,
    exact HN -- assumption -- TODO: something funny here; what is 11.source.to_has_le_2?
  end

theorem equiv.trans (s t u : seq) (Hs : regular s) (Ht : regular t) (Hu : regular u)
        (H : s ≡ t) (H2 : t ≡ u) : s ≡ u :=
  begin
    apply eq_of_bdd Hs Hu,
    intros,
    existsi 2 * (2 * j),
    intro n Hn,
    rewrite [-sub_add_cancel (s n) (t n), *sub_eq_add_neg, algebra.add.assoc],
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    have Hst : abs (s n - t n) ≤ (2 * j)⁻¹, from bdd_of_eq H _ _ Hn,
    have Htu : abs (t n - u n) ≤ (2 * j)⁻¹, from bdd_of_eq H2 _ _ Hn,
    rewrite -(add_halves j),
    apply add_le_add,
    exact Hst, exact Htu
  end

-----------------------------------
-- define operations on cauchy sequences. show operations preserve regularity

private definition K (s : seq) : ℕ+ := pnat.pos (ubound (abs (s pone)) + 1 + 1) dec_trivial

private theorem canon_bound {s : seq} (Hs : regular s) (n : ℕ+) : abs (s n) ≤ rat_of_pnat (K s) :=
  calc
    abs (s n) = abs (s n - s pone + s pone) : by rewrite algebra.sub_add_cancel
    ... ≤ abs (s n - s pone) + abs (s pone) : abs_add_le_abs_add_abs
    ... ≤ n⁻¹ + pone⁻¹ + abs (s pone) : algebra.add_le_add_right !Hs
    ... = n⁻¹ + (1 + abs (s pone)) : by rewrite [pone_inv, rat.add.assoc]
    ... ≤ 1 + (1 + abs (s pone)) : algebra.add_le_add_right (inv_le_one n)
    ... = abs (s pone) + (1 + 1) :
      by rewrite [add.comm 1 (abs (s pone)), rat.add.comm 1, rat.add.assoc]
    ... ≤ of_nat (ubound (abs (s pone))) + (1 + 1) : algebra.add_le_add_right (!ubound_ge)
    ... = of_nat (ubound (abs (s pone)) + (1 + 1)) : of_nat_add
    ... = of_nat (ubound (abs (s pone)) + 1 + 1)   : algebra.add.assoc
    ... = rat_of_pnat (K s)                        : by esimp

theorem bdd_of_regular {s : seq} (H : regular s) : ∃ b : ℚ, ∀ n : ℕ+, s n ≤ b :=
  begin
    existsi rat_of_pnat (K s),
    intros,
    apply rat.le.trans,
    apply le_abs_self,
    apply canon_bound H
  end

theorem bdd_of_regular_strict {s : seq} (H : regular s) : ∃ b : ℚ, ∀ n : ℕ+, s n < b :=
  begin
    cases bdd_of_regular H with [b, Hb],
    existsi b + 1,
    intro n,
    apply rat.lt_of_le_of_lt,
    apply Hb,
    apply algebra.lt_add_of_pos_right,
    apply zero_lt_one
  end

definition K₂ (s t : seq) := max (K s) (K t)

private theorem K₂_symm (s t : seq) : K₂ s t = K₂ t s :=
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
    apply add_le_add,
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
    apply add_le_add,
    rewrite abs_mul,
    apply mul_le_mul_of_nonneg_right,
    apply canon_2_bound_left s t Hs,
    apply abs_nonneg,
    rewrite abs_mul,
    apply mul_le_mul_of_nonneg_left,
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
    rewrite [sub_add_eq_sub_sub, algebra.add_sub_cancel, algebra.sub_self, abs_zero],
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
    apply algebra.add_le_add_right,
    apply inv_two_mul_le_inv,
    rewrite [-(add_halves (2 * n)), -(add_halves n), factor_lemma_2],
    apply add_le_add,
    apply Hs,
    apply Hu
  end

theorem s_mul_comm (s t : seq) : smul s t ≡ smul t s :=
  begin
    rewrite ↑smul,
    intros n,
    rewrite [*(K₂_symm s t), rat.mul.comm, algebra.sub_self, abs_zero],
    apply add_invs_nonneg
  end

private definition DK (s t : seq) := (K₂ s t) * 2
private theorem DK_rewrite (s t : seq) : (K₂ s t) * 2 = DK s t := rfl

private definition TK (s t u : seq) := (DK (λ (n : ℕ+), s (mul (DK s t) n) * t (mul (DK s t) n)) u)

private theorem TK_rewrite (s t u : seq) :
        (DK (λ (n : ℕ+), s (mul (DK s t) n) * t (mul (DK s t) n)) u) = TK s t u := rfl

private theorem s_mul_assoc_lemma (s t u : seq) (a b c d : ℕ+) :
        abs (s a * t a * u b - s c * t d * u d) ≤ abs (t a) * abs (u b) * abs (s a - s c) +
               abs (s c) * abs (t a) * abs (u b - u d) + abs (s c) * abs (u d) * abs (t a - t d) :=
  begin
    rewrite (rewrite_helper7 _ _ _ _ (s c)),
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    rewrite rat.add.assoc,
    apply add_le_add,
    rewrite 2 abs_mul,
    apply rat.le.refl,
    rewrite [*rat.mul.assoc, -algebra.mul_sub_left_distrib, -left_distrib, abs_mul],
    apply mul_le_mul_of_nonneg_left,
    rewrite rewrite_helper,
    apply rat.le.trans,
    apply abs_add_le_abs_add_abs,
    apply add_le_add,
    rewrite abs_mul, apply rat.le.refl,
    rewrite [abs_mul, rat.mul.comm], apply rat.le.refl,
    apply abs_nonneg
  end

private definition Kq (s : seq) := rat_of_pnat (K s) + 1
private theorem Kq_bound {s : seq} (H : regular s) : ∀ n, abs (s n) ≤ Kq s :=
  begin
    intros,
    apply rat.le_of_lt,
    apply rat.lt_of_le_of_lt,
    apply canon_bound H,
    apply algebra.lt_add_of_pos_right,
    apply rat.zero_lt_one
  end

private theorem Kq_bound_nonneg {s : seq} (H : regular s) : 0 ≤ Kq s :=
  rat.le.trans !abs_nonneg (Kq_bound H 2)

private theorem Kq_bound_pos {s : seq} (H : regular s) : 0 < Kq s :=
  have H1 : 0 ≤ rat_of_pnat (K s), from rat.le.trans (!abs_nonneg) (canon_bound H 2),
  add_pos_of_nonneg_of_pos H1 rat.zero_lt_one

private theorem s_mul_assoc_lemma_5 {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
    (a b c : ℕ+) : abs (t a) * abs (u b) * abs (s a - s c) ≤ (Kq t) * (Kq u) * (a⁻¹ + c⁻¹) :=
  begin
    repeat apply algebra.mul_le_mul,
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

private theorem s_mul_assoc_lemma_2 {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
  (a b c d : ℕ+) :
     abs (t a) * abs (u b) * abs (s a - s c) + abs (s c) * abs (t a) * abs (u b - u d)
               + abs (s c) * abs (u d) * abs (t a - t d) ≤
    (Kq t) * (Kq u) * (a⁻¹ + c⁻¹) + (Kq s) * (Kq t) * (b⁻¹ + d⁻¹) + (Kq s) * (Kq u) * (a⁻¹ + d⁻¹) :=
  begin
    apply add_le_add_three,
    repeat (assumption | apply algebra.mul_le_mul | apply Kq_bound | apply Kq_bound_nonneg |
           apply abs_nonneg),
    apply Hs,
    apply abs_nonneg,
    apply rat.mul_nonneg,
    repeat (assumption | apply algebra.mul_le_mul | apply Kq_bound | apply Kq_bound_nonneg |
           apply abs_nonneg),
    apply Hu,
    apply abs_nonneg,
    apply rat.mul_nonneg,
    repeat (assumption | apply algebra.mul_le_mul | apply Kq_bound | apply Kq_bound_nonneg |
           apply abs_nonneg),
    apply Ht,
    apply abs_nonneg,
    apply rat.mul_nonneg,
    repeat (apply Kq_bound_nonneg; assumption)
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
    apply exists.intro,
    intros,
    rewrite [↑smul, *DK_rewrite, *TK_rewrite, -*pnat.mul.assoc, -*rat.mul.assoc],
    apply rat.le.trans,
    apply s_mul_assoc_lemma,
    apply rat.le.trans,
    apply s_mul_assoc_lemma_2,
    apply Hs,
    apply Ht,
    apply Hu,
    rewrite [*s_mul_assoc_lemma_3, -distrib_three_right],
    apply s_mul_assoc_lemma_4,
    apply a,
    repeat apply add_pos,
    repeat apply mul_pos,
    apply Kq_bound_pos Ht,
    apply Kq_bound_pos Hu,
    apply add_pos,
    repeat apply inv_pos,
    repeat apply rat.mul_pos,
    apply Kq_bound_pos Hs,
    apply Kq_bound_pos Ht,
    apply add_pos,
    repeat apply inv_pos,
    repeat apply rat.mul_pos,
    apply Kq_bound_pos Hs,
    apply Kq_bound_pos Hu,
    apply add_pos,
    repeat apply inv_pos,
    apply a_1
  end

theorem zero_is_reg : regular zero :=
  begin
    rewrite [↑regular, ↑zero],
    intros,
    rewrite [algebra.sub_zero, abs_zero],
    apply add_invs_nonneg
  end

theorem s_zero_add (s : seq) (H : regular s) : sadd zero s ≡ s :=
  begin
    rewrite [↑sadd, ↑zero, ↑equiv, ↑regular at H],
    intros,
    rewrite [rat.zero_add],
    apply rat.le.trans,
    apply H,
    apply add_le_add,
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
    apply add_le_add,
    apply inv_two_mul_le_inv,
    apply rat.le.refl
  end

theorem s_neg_cancel (s : seq) (H : regular s) : sadd (sneg s) s ≡ zero :=
  begin
    rewrite [↑sadd, ↑sneg, ↑regular at H, ↑zero, ↑equiv],
    intros,
    rewrite [neg_add_eq_sub, algebra.sub_self, algebra.sub_zero, abs_zero],
    apply add_invs_nonneg
  end

theorem neg_s_cancel (s : seq) (H : regular s) : sadd s (sneg s) ≡ zero :=
  begin
    apply equiv.trans,
    rotate 3,
    apply s_add_comm,
    apply s_neg_cancel s H,
    repeat (apply reg_add_reg | apply reg_neg_reg | assumption),
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
    apply add_le_add,
    apply Esu,
    apply Etv
  end

set_option tactic.goal_names false
private theorem mul_bound_helper {s t : seq} (Hs : regular s) (Ht : regular t) (a b c : ℕ+) (j : ℕ+) :
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
        rewrite -left_distrib,
        apply rat.le.trans,
        apply mul_le_mul_of_nonneg_right,
        apply pceil_helper Hn,
        { repeat (apply algebra.mul_pos | apply algebra.add_pos | apply rat_of_pnat_is_pos |
                  apply pnat.inv_pos) },
        apply rat.le_of_lt,
        apply add_pos,
        apply rat.mul_pos,
        apply rat_of_pnat_is_pos,
        apply add_pos,
        apply pnat.inv_pos,
        apply pnat.inv_pos,
        apply rat.mul_pos,
        apply add_pos,
        apply pnat.inv_pos,
        apply pnat.inv_pos,
        apply rat_of_pnat_is_pos,
        have H : (rat_of_pnat (K s) * (b⁻¹ + c⁻¹) + (a⁻¹ + c⁻¹) * rat_of_pnat (K t)) ≠ 0, begin
          apply ne_of_gt,
          repeat (apply algebra.mul_pos | apply algebra.add_pos | apply rat_of_pnat_is_pos | apply pnat.inv_pos),
        end,
        rewrite (!div_helper H),
        apply rat.le.refl
    end,
    apply add_le_add,
    rewrite [-algebra.mul_sub_left_distrib, abs_mul],
    apply rat.le.trans,
    apply algebra.mul_le_mul,
    apply canon_bound,
    apply Hs,
    apply Ht,
    apply abs_nonneg,
    apply rat.le_of_lt,
    apply rat_of_pnat_is_pos,
    rewrite [*inv_mul_eq_mul_inv, -right_distrib, -rat.mul.assoc, rat.mul.comm],
    apply mul_le_mul_of_nonneg_left,
    apply rat.le.refl,
    apply rat.le_of_lt,
    apply inv_pos,
    rewrite [-algebra.mul_sub_right_distrib, abs_mul],
    apply rat.le.trans,
    apply algebra.mul_le_mul,
    apply Hs,
    apply canon_bound,
    apply Ht,
    apply abs_nonneg,
    apply add_invs_nonneg,
    rewrite [*inv_mul_eq_mul_inv, -right_distrib, mul.comm _ n⁻¹, rat.mul.assoc],
    apply algebra.mul_le_mul,
    repeat apply rat.le.refl,
    apply rat.le_of_lt,
    apply rat.mul_pos,
    apply add_pos,
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
    apply add_le_add,
    apply HN1,
    apply pnat.le.trans,
    apply max_left N1 N2,
    apply Hn,
    apply HN2,
    apply pnat.le.trans,
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
                            (div_pos_of_pos_of_pos Hε (Kq_bound_pos Hs)),
    cases Bd with [N, HN],
    existsi N,
    intro n Hn,
    rewrite [↑equiv at Htz, ↑zero at *, algebra.sub_zero, ↑smul, abs_mul],
    apply rat.le.trans,
    apply algebra.mul_le_mul,
    apply Kq_bound Hs,
    have HN' : ∀ (n : ℕ+), N ≤ n → abs (t n) ≤ ε / Kq s,
      from λ n, (eq.subst (sub_zero (t n)) (HN n)),
    apply HN',
    apply le.trans Hn,
    apply pnat.mul_le_mul_left,
    apply abs_nonneg,
    apply rat.le_of_lt (Kq_bound_pos Hs),
    rewrite (mul_div_cancel' (ne.symm (ne_of_lt (Kq_bound_pos Hs)))),
    apply rat.le.refl
  end

private theorem neg_bound_eq_bound (s : seq) : K (sneg s) = K s  :=
  by rewrite [↑K, ↑sneg, abs_neg]

private theorem neg_bound2_eq_bound2 (s t : seq) : K₂ s (sneg t) = K₂ s t :=
  by rewrite [↑K₂, neg_bound_eq_bound]

private theorem sneg_def (s : seq) : (λ (n : ℕ+), -(s n)) = sneg s := rfl

theorem mul_neg_equiv_neg_mul {s t : seq} : smul s (sneg t) ≡ sneg (smul s t) :=
  begin
    rewrite [↑equiv, ↑smul],
    intros,
    rewrite [↑sneg, *sub_neg_eq_add, -neg_mul_eq_mul_neg, rat.add.comm, *sneg_def,
             *neg_bound2_eq_bound2, algebra.add.right_inv, abs_zero],
    apply add_invs_nonneg
  end

theorem equiv_of_diff_equiv_zero {s t : seq} (Hs : regular s) (Ht : regular t)
        (H : sadd s (sneg t) ≡ zero) : s ≡ t :=
  begin
    have hsimp : ∀ a b c d e : ℚ, a + b + c + (d + e) = b + d + a + e + c, from
     λ a b c d e, calc
         a + b + c + (d + e) = a + b + (d + e) + c : algebra.add.right_comm
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
    let He' := λ a b c, eq.subst !algebra.sub_zero (He a b c),
    apply (He' _ _ Hn),
    apply Ht,
    rewrite [hsimp, add_halves, -(add_halves j), -(add_halves (2 * j)), -*rat.add.assoc],
    apply algebra.add_le_add_right,
    apply add_le_add_three,
    repeat (apply rat.le.trans; apply inv_ge_of_le Hn; apply inv_two_mul_le_inv)
  end

theorem s_sub_cancel (s : seq) : sadd s (sneg s) ≡ zero :=
  begin
    rewrite [↑equiv, ↑sadd, ↑sneg, ↑zero],
    intros,
    rewrite [algebra.sub_zero, algebra.add.right_inv, abs_zero],
    apply add_invs_nonneg
  end

theorem diff_equiv_zero_of_equiv {s t : seq} (Hs : regular s) (Ht : regular t) (H : s ≡ t) :
        sadd s (sneg t) ≡ zero :=
  begin
    apply equiv.trans,
    rotate 4,
    apply s_sub_cancel t,
    rotate 2,
    apply zero_is_reg,
    apply add_well_defined,
    repeat (assumption | apply reg_neg_reg),
    apply equiv.refl,
    repeat (assumption | apply reg_add_reg | apply reg_neg_reg)
  end

private theorem mul_well_defined_half1 {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
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

private theorem mul_well_defined_half2 {s t u : seq} (Hs : regular s) (Ht : regular t) (Hu : regular u)
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
    rewrite [algebra.sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem s_one_mul {s : seq} (H : regular s) : smul one s ≡ s :=
  begin
    intros,
    rewrite [↑smul, ↑one, rat.one_mul],
    apply rat.le.trans,
    apply H,
    apply algebra.add_le_add_right,
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
    rewrite [algebra.zero_sub at H, abs_neg at H, add_halves at H],
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
    rewrite [↑const, algebra.sub_self, abs_zero],
    apply add_invs_nonneg
  end

theorem add_consts (a b : ℚ) : sadd (const a) (const b) ≡ const (a + b) :=
  by apply equiv.refl

theorem mul_consts (a b : ℚ) : smul (const a) (const b) ≡ const (a * b) :=
  by apply equiv.refl

theorem neg_const (a : ℚ) : sneg (const a) ≡ const (-a) :=
  by apply equiv.refl

section
  open rat

  lemma eq_of_const_equiv {a b : ℚ} (H : const a ≡ const b) : a = b :=
  have H₁ : ∀ n : ℕ+, abs (a - b) ≤ n⁻¹ + n⁻¹, from H,
  eq_of_forall_abs_sub_le
    (take ε,
      suppose ε > 0,
      have ε / 2 > 0, from div_pos_of_pos_of_pos this two_pos,
      obtain n (Hn : n⁻¹ ≤ ε / 2), from pnat_bound this,
      show abs (a - b) ≤ ε, from calc
        abs (a - b) ≤ n⁻¹ + n⁻¹     : H₁ n
                ... ≤ ε / 2 + ε / 2 : add_le_add Hn Hn
                ... = ε             : algebra.add_halves)
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
infix + := radd

definition rmul (s t : reg_seq) : reg_seq :=
  reg_seq.mk (smul (reg_seq.sq s) (reg_seq.sq t))
             (reg_mul_reg (reg_seq.is_reg s) (reg_seq.is_reg t))
infix * := rmul

definition rneg (s : reg_seq) : reg_seq :=
  reg_seq.mk (sneg (reg_seq.sq s)) (reg_neg_reg (reg_seq.is_reg s))
prefix - := rneg

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

theorem r_mul_consts (a b : ℚ) : requiv (r_const a * r_const b) (r_const (a * b)) := mul_consts a b

theorem r_neg_const (a : ℚ) : requiv (-r_const a) (r_const (-a)) := neg_const a

end rat_seq
----------------------------------------------
-- take quotients to get ℝ and show it's a comm ring

open rat_seq
definition real := quot reg_seq.to_setoid
namespace real
notation `ℝ` := real

protected definition prio := num.pred rat.prio

protected definition add (x y : ℝ) : ℝ :=
  (quot.lift_on₂ x y (λ a b, quot.mk (a + b))
                     (take a b c d : reg_seq, take Hab : requiv a c, take Hcd : requiv b d,
                       quot.sound (radd_well_defined Hab Hcd)))

--infix [priority real.prio] + := add

protected definition mul (x y : ℝ) : ℝ :=
  (quot.lift_on₂ x y (λ a b, quot.mk (a * b))
                     (take a b c d : reg_seq, take Hab : requiv a c, take Hcd : requiv b d,
                       quot.sound (rmul_well_defined Hab Hcd)))
--infix [priority real.prio] * := mul

protected definition neg (x : ℝ) : ℝ :=
  (quot.lift_on x (λ a, quot.mk (-a)) (take a b : reg_seq, take Hab : requiv a b,
                                   quot.sound (rneg_well_defined Hab)))
--prefix [priority real.prio] `-` := neg

definition real_has_add [reducible] [instance] [priority real.prio] : has_add real :=
has_add.mk real.add

definition real_has_mul [reducible] [instance] [priority real.prio] : has_mul real :=
has_mul.mk real.mul

definition real_has_neg [reducible] [instance] [priority real.prio] : has_neg real :=
has_neg.mk real.neg

protected definition sub [reducible] (a b : ℝ) : real := a + (-b)

definition real_has_sub [reducible] [instance] [priority real.prio] : has_sub real :=
has_sub.mk real.sub

open rat -- no coercions before

definition of_rat [coercion] (a : ℚ) : ℝ := quot.mk (r_const a)
definition of_int [coercion] (i : ℤ) : ℝ := int.to.real i
definition of_nat [coercion] (n : ℕ) : ℝ := nat.to.real n
definition of_num [coercion] [reducible] (n : num) : ℝ := of_rat (rat.of_num n)

definition real_has_zero [reducible] [instance] [priority real.prio] : has_zero real :=
has_zero.mk (0:rat)

definition real_has_one [reducible] [instance] [priority real.prio] : has_one real :=
has_one.mk (1:rat)

theorem real_zero_eq_rat_zero : (0:real) = of_rat (0:rat) :=
rfl

theorem real_one_eq_rat_one : (1:real) = of_rat (1:rat) :=
rfl

theorem add_comm (x y : ℝ) : x + y = y + x :=
  quot.induction_on₂ x y (λ s t, quot.sound (r_add_comm s t))

theorem add_assoc (x y z : ℝ) : x + y + z = x + (y + z) :=
  quot.induction_on₃ x y z (λ s t u, quot.sound (r_add_assoc s t u))

theorem zero_add (x : ℝ) : 0 + x = x :=
  quot.induction_on x (λ s, quot.sound (r_zero_add s))

theorem add_zero (x : ℝ) : x + 0 = x :=
  quot.induction_on x (λ s, quot.sound (r_add_zero s))

theorem neg_cancel (x : ℝ) : -x + x = 0 :=
  quot.induction_on x (λ s, quot.sound (r_neg_cancel s))

theorem mul_assoc (x y z : ℝ) : x * y * z = x * (y * z) :=
  quot.induction_on₃ x y z (λ s t u, quot.sound (r_mul_assoc s t u))

theorem mul_comm (x y : ℝ) : x * y = y * x :=
  quot.induction_on₂ x y (λ s t, quot.sound (r_mul_comm s t))

theorem one_mul (x : ℝ) : 1 * x = x :=
  quot.induction_on x (λ s, quot.sound (r_one_mul s))

theorem mul_one (x : ℝ) : x * 1 = x :=
  quot.induction_on x (λ s, quot.sound (r_mul_one s))

theorem left_distrib (x y z : ℝ) : x * (y + z) = x * y + x * z :=
  quot.induction_on₃ x y z (λ s t u, quot.sound (r_distrib s t u))

theorem right_distrib (x y z : ℝ) : (x + y) * z = x * z + y * z :=
  by rewrite [mul_comm, left_distrib, {x * _}mul_comm, {y * _}mul_comm] -- this shouldn't be necessary

theorem zero_ne_one : ¬ (0 : ℝ) = 1 :=
  take H : 0 = 1,
  absurd (quot.exact H) (r_zero_nequiv_one)

protected definition comm_ring [reducible] : algebra.comm_ring ℝ :=
  begin
    fapply algebra.comm_ring.mk,
    exact add,
    exact add_assoc,
    exact of_num 0,
    exact zero_add,
    exact add_zero,
    exact neg,
    exact neg_cancel,
    exact add_comm,
    exact mul,
    exact mul_assoc,
    apply of_num 1,
    apply one_mul,
    apply mul_one,
    apply left_distrib,
    apply right_distrib,
    apply mul_comm
  end

theorem of_int_eq (a : ℤ) : of_int a = of_rat (rat.of_int a) := rfl

theorem of_nat_eq (a : ℕ) : of_nat a = of_rat (rat.of_nat a) := rfl

theorem of_rat.inj {x y : ℚ} (H : of_rat x = of_rat y) : x = y :=
eq_of_const_equiv (quot.exact H)

theorem eq_of_of_rat_eq_of_rat {x y : ℚ} (H : of_rat x = of_rat y) : x = y :=
of_rat.inj H

theorem of_rat_eq_of_rat_iff (x y : ℚ) : of_rat x = of_rat y ↔ x = y :=
iff.intro eq_of_of_rat_eq_of_rat !congr_arg

theorem of_int.inj {a b : ℤ} (H : of_int a = of_int b) : a = b :=
rat.of_int.inj (of_rat.inj H)

theorem eq_of_of_int_eq_of_int {a b : ℤ} (H : of_int a = of_int b) : a = b :=
of_int.inj H

theorem of_int_eq_of_int_iff (a b : ℤ) : of_int a = of_int b ↔ a = b :=
iff.intro of_int.inj !congr_arg

theorem of_nat.inj {a b : ℕ} (H : of_nat a = of_nat b) : a = b :=
int.of_nat.inj (of_int.inj H)

theorem eq_of_of_nat_eq_of_nat {a b : ℕ} (H : of_nat a = of_nat b) : a = b :=
of_nat.inj H

theorem of_nat_eq_of_nat_iff (a b : ℕ) : of_nat a = of_nat b ↔ a = b :=
iff.intro of_nat.inj !congr_arg

theorem of_rat_add (a b : ℚ) : of_rat (a + b) = of_rat a + of_rat b :=
   quot.sound (r_add_consts a b)

theorem of_rat_neg (a : ℚ) : of_rat (-a) = -of_rat a :=
  eq.symm (quot.sound (r_neg_const a))

theorem of_rat_mul (a b : ℚ) : of_rat (a * b) = of_rat a * of_rat b :=
  quot.sound (r_mul_consts a b)

open int

theorem of_int_add (a b : ℤ) : of_int (a + b) = of_int a + of_int b :=
  by rewrite [of_int_eq, rat.of_int_add, of_rat_add]

theorem of_int_neg (a : ℤ) : of_int (-a) = -of_int a :=
  by rewrite [of_int_eq, rat.of_int_neg, of_rat_neg]

theorem of_int_mul (a b : ℤ) : of_int (a * b) = of_int a * of_int b :=
  by rewrite [of_int_eq, rat.of_int_mul, of_rat_mul]

theorem of_nat_add (a b : ℕ) : of_nat (a + b) = of_nat a + of_nat b :=
  by rewrite [of_nat_eq, rat.of_nat_add, of_rat_add]

theorem of_nat_mul (a b : ℕ) : of_nat (a * b) = of_nat a * of_nat b :=
  by rewrite [of_nat_eq, rat.of_nat_mul, of_rat_mul]

theorem add_half_of_rat (n : ℕ+) : of_rat (2 * n)⁻¹ + of_rat (2 * n)⁻¹ = of_rat (n⁻¹) :=
  by rewrite [-of_rat_add, pnat.add_halves]

theorem one_add_one : 1 + 1 = (2 : ℝ) := rfl

end real
