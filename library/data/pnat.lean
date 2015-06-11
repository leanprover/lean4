/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Basic facts about the positive natural numbers.

Developed primarily for use in the construction of ℝ. For the most part, the only theorems here
are those needed for that construction.

-/

import data.rat.order data.nat
open nat rat

section pnat

inductive pnat : Type :=
  pos : Π n : nat, n > 0 → pnat

notation `ℕ+` := pnat

definition nat_of_pnat (p : pnat) : ℕ :=
  pnat.rec_on p (λ n H, n)
local postfix `~` : std.prec.max_plus := nat_of_pnat

theorem nat_of_pnat_pos (p : pnat) : p~ > 0 :=
  pnat.rec_on p (λ n H, H)

definition add (p q : pnat) : pnat :=
  pnat.pos (p~ + q~) (nat.add_pos (nat_of_pnat_pos p) (nat_of_pnat_pos q))
infix `+` := add

definition mul (p q : pnat) : pnat :=
  pnat.pos (p~ * q~) (nat.mul_pos (nat_of_pnat_pos p) (nat_of_pnat_pos q))
infix `*` := mul

definition le (p q : pnat) := p~ ≤ q~
infix `≤` := le
notation p `≥` q := q ≤ p

definition lt (p q : pnat) := p~ < q~
infix `<` := lt

protected theorem pnat.eq {p q : ℕ+} : p~ = q~ → p = q :=
  pnat.cases_on p (λ p' Hp, pnat.cases_on q (λ q' Hq,
  begin
    rewrite ↑nat_of_pnat,
    intro H,
    generalize Hp,
    generalize Hq,
    rewrite H,
    intro Hp Hq,
    apply rfl
  end))

definition pnat_le_decidable [instance] (p q : pnat) : decidable (p ≤ q) :=
  pnat.rec_on p (λ n H, pnat.rec_on q
    (λ m H2, if Hl : n ≤ m then decidable.inl Hl else decidable.inr Hl))

definition pnat_lt_decidable [instance] {p q : pnat} : decidable (p < q) :=
  pnat.rec_on p (λ n H, pnat.rec_on q
    (λ m H2, if Hl : n < m then decidable.inl Hl else decidable.inr Hl))

theorem ple.trans {p q r : pnat} (H1 : p ≤ q) (H2 : q ≤ r) : p ≤ r := nat.le.trans H1 H2

definition max (p q : pnat) :=
  pnat.pos (nat.max (p~) (q~)) (nat.lt_of_lt_of_le (!nat_of_pnat_pos) (!le_max_right))

theorem max_right (a b : ℕ+) : max a b ≥ b := !le_max_right

theorem max_left (a b : ℕ+) : max a b ≥ a := !le_max_left

theorem max_eq_right {a b : ℕ+} (H : a < b) : max a b = b :=
  have Hnat : nat.max a~ b~ = b~, from nat.max_eq_right H,
  pnat.eq Hnat

theorem max_eq_left {a b : ℕ+} (H : ¬ a < b) : max a b = a :=
  have Hnat : nat.max a~ b~ = a~, from nat.max_eq_left H,
  pnat.eq Hnat

theorem pnat.le_of_lt {a b : ℕ+} (H : a < b) : a ≤ b := nat.le_of_lt H

theorem pnat.not_lt_of_le {a b : ℕ+} (H : a ≤ b) : ¬ (b < a) := nat.not_lt_of_ge H

theorem pnat.le_of_not_lt {a b : ℕ+} (H : ¬ a < b) : b ≤ a := nat.le_of_not_gt H

theorem pnat.eq_of_le_of_ge {a b : ℕ+} (H1 : a ≤ b) (H2 : b ≤ a) : a = b :=
  pnat.eq (nat.eq_of_le_of_ge H1 H2)

theorem pnat.le.refl (a : ℕ+) : a ≤ a := !nat.le.refl

notation 2 := pnat.pos 2 dec_trivial
notation 3 := pnat.pos 3 dec_trivial
definition pone : pnat := pnat.pos 1 dec_trivial

definition pnat.to_rat [reducible] (n : ℕ+) : ℚ :=
  pnat.rec_on n (λ n H, of_nat n)

theorem pnat.to_rat_of_nat (n : ℕ+) : pnat.to_rat n = of_nat n~ :=
  pnat.rec_on n (λ n H, rfl)

-- these will come in rat

theorem rat_of_nat_nonneg (n : ℕ) : 0 ≤ of_nat n := trivial

theorem rat_of_pnat_ge_one (n : ℕ+) : pnat.to_rat n ≥ 1 :=
  pnat.rec_on n (λ m h, (iff.mp' !of_nat_le_of_nat) (succ_le_of_lt h))

theorem rat_of_pnat_is_pos (n : ℕ+) : pnat.to_rat n > 0 :=
  pnat.rec_on n (λ m h, (iff.mp' !of_nat_pos) h)

theorem of_nat_le_of_nat_of_le {m n : ℕ} (H : m ≤ n) : of_nat m ≤ of_nat n :=
  (iff.mp' !of_nat_le_of_nat) H

theorem of_nat_lt_of_nat_of_lt {m n : ℕ} (H : m < n) : of_nat m < of_nat n :=
  (iff.mp' !of_nat_lt_of_nat) H

theorem pnat_le_to_rat_le {m n : ℕ+} (H : m ≤ n) : pnat.to_rat m ≤ pnat.to_rat n :=
  begin
    rewrite *pnat.to_rat_of_nat,
    apply of_nat_le_of_nat_of_le H
  end

theorem pnat_lt_to_rat_lt {m n : ℕ+} (H : m < n) : pnat.to_rat m < pnat.to_rat n :=
  begin
    rewrite *pnat.to_rat_of_nat,
    apply of_nat_lt_of_nat_of_lt H
  end

theorem rat_le_to_pnat_le {m n : ℕ+} (H : pnat.to_rat m ≤ pnat.to_rat n) : m ≤ n :=
  begin
    rewrite *pnat.to_rat_of_nat at H,
    apply (iff.mp !of_nat_le_of_nat) H
  end

definition inv (n : ℕ+) : ℚ := (1 : ℚ) / pnat.to_rat n
postfix `⁻¹` := inv

theorem inv_pos (n : ℕ+) : n⁻¹ > 0 := div_pos_of_pos !rat_of_pnat_is_pos

theorem inv_le_one (n : ℕ+) : n⁻¹ ≤ (1 : ℚ) :=
  begin
    rewrite [↑inv, -one_div_one],
    apply div_le_div_of_le,
    apply rat.zero_lt_one,
    apply rat_of_pnat_ge_one
  end

theorem inv_lt_one_of_gt {n : ℕ+} (H : n~ > 1) : n⁻¹ < (1 : ℚ) :=
  begin
    rewrite [↑inv, -one_div_one],
    apply div_lt_div_of_lt,
    apply rat.zero_lt_one,
    rewrite pnat.to_rat_of_nat,
    apply (of_nat_lt_of_nat_of_lt H)
  end

theorem pone_inv : pone⁻¹ = 1 := rfl

theorem add_invs_nonneg (m n : ℕ+) : 0 ≤ m⁻¹ + n⁻¹ :=
  begin
    apply rat.le_of_lt,
    apply rat.add_pos,
    repeat apply inv_pos
  end

set_option pp.coercions true

theorem pnat_one_mul (n : ℕ+) : pone * n = n :=
  begin
    apply pnat.eq,
    rewrite [↑pone, ↑mul, ↑nat_of_pnat, one_mul]
  end

theorem pone_le (n : ℕ+) : pone ≤ n :=
  succ_le_of_lt (nat_of_pnat_pos n)

theorem pnat_to_rat_mul (a b : ℕ+) : pnat.to_rat (a * b) = pnat.to_rat a * pnat.to_rat b :=
  by rewrite *pnat.to_rat_of_nat

theorem mul_lt_mul_left (a b c : ℕ+) (H : a < b) : a * c < b * c :=
   nat.mul_lt_mul_of_pos_right H !nat_of_pnat_pos

theorem half_shrink_strong (n : ℕ+) : (2 * n)⁻¹ < n⁻¹ :=
  begin
    rewrite ↑inv,
    apply div_lt_div_of_lt,
    apply rat_of_pnat_is_pos,
    have H : n~ < (2 * n)~, begin
      rewrite -pnat_one_mul at {1},
      apply mul_lt_mul_left,
      apply dec_trivial
    end,
    rewrite *pnat.to_rat_of_nat,
    apply of_nat_lt_of_nat_of_lt,
    apply H
  end

theorem half_shrink (n : ℕ+) : (2 * n)⁻¹ ≤ n⁻¹ := le_of_lt !half_shrink_strong

theorem inv_ge_of_le {p q : ℕ+} (H : p ≤ q) : q⁻¹ ≤ p⁻¹ :=
  div_le_div_of_le !rat_of_pnat_is_pos (pnat_le_to_rat_le H)

theorem inv_gt_of_lt {p q : ℕ+} (H : p < q) : q⁻¹ < p⁻¹ :=
  div_lt_div_of_lt !rat_of_pnat_is_pos (pnat_lt_to_rat_lt H)

theorem ge_of_inv_le {p q : ℕ+} (H : p⁻¹ ≤ q⁻¹) : q ≤ p :=
  rat_le_to_pnat_le (le_of_div_le !rat_of_pnat_is_pos H)

theorem two_mul (p : ℕ+) : pnat.to_rat (2 * p) = (1 + 1) * pnat.to_rat p :=
  by rewrite pnat_to_rat_mul

theorem padd_halves (p : ℕ+) : (2 * p)⁻¹ + (2 * p)⁻¹ = p⁻¹ :=
  begin
    rewrite [↑inv, -(@add_halves (1 / (pnat.to_rat p))), *div_div_eq_div_mul'],
    have H : pnat.to_rat (2 * p) = pnat.to_rat p * (1 + 1), by rewrite [rat.mul.comm, two_mul],
    rewrite *H
  end

theorem add_halves_double (m n : ℕ+) :
        m⁻¹ + n⁻¹ = ((2 * m)⁻¹ + (2 * n)⁻¹) + ((2 * m)⁻¹ + (2 * n)⁻¹) :=
  have simp [visible] : ∀ a b : ℚ, (a + a) + (b + b) = (a + b) + (a + b),
    by intros; rewrite [rat.add.assoc, -(rat.add.assoc a b b), {_+b}rat.add.comm, -*rat.add.assoc],
  by rewrite [-padd_halves m, -padd_halves n, simp]

theorem pnat_div_helper {p q : ℕ+} : (p * q)⁻¹ = p⁻¹ * q⁻¹ :=
  by rewrite [↑inv, pnat_to_rat_mul, one_div_mul_one_div''']

theorem inv_mul_le_inv (p q : ℕ+) : (p * q)⁻¹ ≤ q⁻¹ :=
  begin
    rewrite [pnat_div_helper, -{q⁻¹}rat.one_mul at {2}],
    apply rat.mul_le_mul,
    apply inv_le_one,
    apply rat.le.refl,
    apply rat.le_of_lt,
    apply inv_pos,
    apply rat.le_of_lt rat.zero_lt_one
  end

theorem pnat_mul_le_mul_left' (a b c : ℕ+) (H : a ≤ b) : c * a ≤ c * b :=
  nat.mul_le_mul_of_nonneg_left H (le_of_lt !nat_of_pnat_pos)

theorem pnat_mul_assoc (a b c : ℕ+) : a * b * c = a * (b * c) :=
  pnat.eq !nat.mul.assoc

theorem pnat_mul_comm (a b : ℕ+) : a * b = b * a :=
  pnat.eq !nat.mul.comm

theorem pnat_add_assoc (a b c : ℕ+) : a + b + c = a + (b + c) :=
  pnat.eq !nat.add.assoc

theorem pnat.mul_le_mul_left (p q : ℕ+) : q ≤ p * q :=
  begin
    rewrite [-pnat_one_mul at {1}, pnat_mul_comm, pnat_mul_comm p],
    apply pnat_mul_le_mul_left',
    apply pone_le
  end

theorem pnat.mul_le_mul_right (p q : ℕ+) : p ≤ p * q :=
  by rewrite pnat_mul_comm; apply pnat.mul_le_mul_left

theorem one_lt_two : pone < 2 := dec_trivial

theorem pnat.lt_of_not_le {p q : ℕ+} (H : ¬ p ≤ q) : q < p :=
  nat.lt_of_not_ge H

theorem pnat.inv_cancel (p : ℕ+) : pnat.to_rat p * p⁻¹ = (1 : ℚ) :=
  mul_one_div_cancel (ne.symm (rat.ne_of_lt !rat_of_pnat_is_pos))

theorem pnat.inv_cancel_right (p : ℕ+) : p⁻¹ * pnat.to_rat p = (1 : ℚ) :=
  by rewrite rat.mul.comm; apply pnat.inv_cancel

theorem pnat_lt_add_left (p q : ℕ+) : p < p + q :=
  begin
    have H : p~ < p~ + q~, begin
      rewrite -nat.add_zero at {1},
      apply nat.add_lt_add_left,
      apply nat_of_pnat_pos
    end,
    apply H
  end

theorem inv_add_lt_left (p q : ℕ+) : (p + q)⁻¹ < p⁻¹ :=
  by apply inv_gt_of_lt; apply pnat_lt_add_left

theorem div_le_pnat (q : ℚ) (n : ℕ+) (H : q ≥ n⁻¹) : 1 / q ≤ pnat.to_rat n :=
  begin
    apply rat.div_le_of_le_mul,
    apply rat.lt_of_lt_of_le,
    apply inv_pos,
    rotate 1,
    apply H,
    apply rat.le_mul_of_div_le,
    apply rat_of_pnat_is_pos,
    apply H
  end

theorem pnat_cancel' (n m : ℕ+) : (n * n * m)⁻¹ * (pnat.to_rat n * pnat.to_rat n) = m⁻¹ :=
  begin
    have simp : ∀ a b c : ℚ, (a * a * (b * b * c)) = (a * b) * (a * b) * c, from sorry, -- simp
    rewrite [rat.mul.comm, *pnat_div_helper, simp, *pnat.inv_cancel, *rat.one_mul]
  end


end pnat
