/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Basic facts about the positive natural numbers.

Developed primarily for use in the construction of ℝ. For the most part, the only theorems here
are those needed for that construction.
-/
import data.rat.order data.nat
open nat rat subtype eq.ops
open algebra

namespace pnat

definition pnat := { n : ℕ | n > 0 }

notation `ℕ+` := pnat

definition pos (n : ℕ) (H : n > 0) : ℕ+ := tag n H

definition nat_of_pnat (p : ℕ+) : ℕ := elt_of p
reserve postfix `~`:std.prec.max_plus
local postfix ~ := nat_of_pnat

theorem pnat_pos (p : ℕ+) : p~ > 0 := has_property p

protected definition add (p q : ℕ+) : ℕ+ :=
tag (p~ + q~) (add_pos (pnat_pos p) (pnat_pos q))

protected definition mul (p q : ℕ+) : ℕ+ :=
tag (p~ * q~) (mul_pos (pnat_pos p) (pnat_pos q))

protected definition le (p q : ℕ+) := p~ ≤ q~

protected definition lt (p q : ℕ+) := p~ < q~

definition pnat_has_add [instance] [reducible] : has_add pnat :=
has_add.mk pnat.add

definition pnat_has_mul [instance] [reducible] : has_mul pnat :=
has_mul.mk pnat.mul

definition pnat_has_le [instance] [reducible] : has_le pnat :=
has_le.mk pnat.le

definition pnat_has_lt [instance] [reducible] : has_lt pnat :=
has_lt.mk pnat.lt

definition pnat_has_one [instance] [reducible] : has_one pnat :=
has_one.mk (pos (1:nat) dec_trivial)

lemma mul.def (p q : ℕ+) : p * q = tag (p~ * q~) (mul_pos (pnat_pos p) (pnat_pos q)) :=
rfl

lemma le.def (p q : ℕ+) : (p ≤ q) = (p~ ≤ q~) :=
rfl

lemma lt.def (p q : ℕ+) : (p < q) = (p~ < q~) :=
rfl

protected theorem pnat.eq {p q : ℕ+} : p~ = q~ → p = q :=
subtype.eq

definition pnat_le_decidable [instance] (p q : ℕ+) : decidable (p ≤ q) :=
begin rewrite le.def, exact nat.decidable_le p~ q~ end

definition pnat_lt_decidable [instance] {p q : ℕ+} : decidable (p < q) :=
begin rewrite lt.def, exact nat.decidable_lt p~ q~ end

theorem le.trans {p q r : ℕ+} : p ≤ q → q ≤ r → p ≤ r :=
begin rewrite +le.def, apply nat.le_trans end

definition max (p q : ℕ+) : ℕ+ :=
tag (max p~ q~) (lt_of_lt_of_le (!pnat_pos) (!le_max_right))

theorem max_right (a b : ℕ+) : max a b ≥ b :=
begin change b ≤ max a b, rewrite le.def, apply le_max_right end

theorem max_left (a b : ℕ+) : max a b ≥ a :=
begin change a ≤ max a b, rewrite le.def, apply le_max_left end

theorem max_eq_right {a b : ℕ+} (H : a < b) : max a b = b :=
begin rewrite lt.def at H, exact pnat.eq (max_eq_right_of_lt H) end

theorem max_eq_left {a b : ℕ+} (H : ¬ a < b) : max a b = a :=
begin rewrite lt.def at H, exact pnat.eq (max_eq_left (le_of_not_gt H)) end

theorem le_of_lt {a b : ℕ+} : a < b → a ≤ b :=
begin rewrite [lt.def, le.def], apply nat.le_of_lt end

theorem not_lt_of_ge {a b : ℕ+} : a ≤ b → ¬ (b < a) :=
begin rewrite [lt.def, le.def], apply not_lt_of_ge end

theorem le_of_not_gt {a b : ℕ+} : ¬ a < b → b ≤ a :=
begin rewrite [lt.def, le.def], apply le_of_not_gt end

theorem eq_of_le_of_ge {a b : ℕ+} : a ≤ b → b ≤ a → a = b :=
begin rewrite [+le.def], intros H1 H2, exact pnat.eq (eq_of_le_of_ge H1 H2) end

theorem le.refl (a : ℕ+) : a ≤ a :=
begin rewrite le.def end

notation 2 := (tag 2 dec_trivial : ℕ+)
notation 3 := (tag 3 dec_trivial : ℕ+)
definition pone : ℕ+ := tag 1 dec_trivial

definition rat_of_pnat [reducible] (n : ℕ+) : ℚ :=
n~

theorem pnat.to_rat_of_nat (n : ℕ+) : rat_of_pnat n = of_nat n~ :=
rfl

-- these will come in rat

theorem rat_of_nat_nonneg (n : ℕ) : 0 ≤ of_nat n :=
trivial

theorem rat_of_pnat_ge_one (n : ℕ+) : rat_of_pnat n ≥ 1 :=
of_nat_le_of_nat_of_le (pnat_pos n)

theorem rat_of_pnat_is_pos (n : ℕ+) : rat_of_pnat n > 0 :=
of_nat_lt_of_nat_of_lt (pnat_pos n)

theorem of_nat_le_of_nat_of_le {m n : ℕ} (H : m ≤ n) : of_nat m ≤ of_nat n :=
of_nat_le_of_nat_of_le H

theorem of_nat_lt_of_nat_of_lt {m n : ℕ} (H : m < n) : of_nat m < of_nat n :=
of_nat_lt_of_nat_of_lt H

theorem rat_of_pnat_le_of_pnat_le {m n : ℕ+} (H : m ≤ n) : rat_of_pnat m ≤ rat_of_pnat n :=
begin rewrite le.def at H, exact of_nat_le_of_nat_of_le H end

theorem rat_of_pnat_lt_of_pnat_lt {m n : ℕ+} (H : m < n) : rat_of_pnat m < rat_of_pnat n :=
begin rewrite lt.def at H, exact of_nat_lt_of_nat_of_lt H end

theorem pnat_le_of_rat_of_pnat_le {m n : ℕ+} (H : rat_of_pnat m ≤ rat_of_pnat n) : m ≤ n :=
begin rewrite le.def, exact le_of_of_nat_le_of_nat H end

definition inv (n : ℕ+) : ℚ :=
(1 : ℚ) / rat_of_pnat n

local postfix `⁻¹` := inv

theorem inv_pos (n : ℕ+) : n⁻¹ > 0 := one_div_pos_of_pos !rat_of_pnat_is_pos

theorem inv_le_one (n : ℕ+) : n⁻¹ ≤ (1 : ℚ) :=
begin
  unfold inv,
  change 1 / rat_of_pnat n ≤ 1 / 1,
  apply one_div_le_one_div_of_le,
  apply algebra.zero_lt_one,
  apply rat_of_pnat_ge_one
end

theorem inv_lt_one_of_gt {n : ℕ+} (H : n~ > 1) : n⁻¹ < (1 : ℚ) :=
begin
  unfold inv,
  change 1 / rat_of_pnat n < 1 / 1,
  apply one_div_lt_one_div_of_lt,
  apply algebra.zero_lt_one,
  rewrite pnat.to_rat_of_nat,
  apply (of_nat_lt_of_nat_of_lt H)
end

theorem pone_inv : pone⁻¹ = 1 := rfl

theorem add_invs_nonneg (m n : ℕ+) : 0 ≤ m⁻¹ + n⁻¹ :=
begin
  apply rat.le_of_lt,
  apply add_pos,
  repeat apply inv_pos
end

theorem one_mul (n : ℕ+) : pone * n = n :=
begin
  apply pnat.eq,
  unfold pone,
  rewrite [mul.def, ↑nat_of_pnat, algebra.one_mul]
end

theorem pone_le (n : ℕ+) : pone ≤ n :=
begin rewrite le.def, exact succ_le_of_lt (pnat_pos n) end

theorem pnat_to_rat_mul (a b : ℕ+) : rat_of_pnat (a * b) = rat_of_pnat a * rat_of_pnat b := rfl

theorem mul_lt_mul_left {a b c : ℕ+} (H : a < b) : a * c < b * c :=
begin rewrite [lt.def at *], exact mul_lt_mul_of_pos_right H !pnat_pos end

theorem one_lt_two : pone < 2 :=
!nat.le_refl

theorem inv_two_mul_lt_inv (n : ℕ+) : (2 * n)⁻¹ < n⁻¹ :=
begin
  rewrite ↑inv,
  apply one_div_lt_one_div_of_lt,
  apply rat_of_pnat_is_pos,
  have H : n~ < (2 * n)~, begin
    rewrite -one_mul at {1},
    rewrite -lt.def,
    apply mul_lt_mul_left,
    apply one_lt_two
  end,
  apply of_nat_lt_of_nat_of_lt,
  apply H
end

theorem inv_two_mul_le_inv (n : ℕ+) : (2 * n)⁻¹ ≤ n⁻¹ := rat.le_of_lt !inv_two_mul_lt_inv

theorem inv_ge_of_le {p q : ℕ+} (H : p ≤ q) : q⁻¹ ≤ p⁻¹ :=
one_div_le_one_div_of_le !rat_of_pnat_is_pos (rat_of_pnat_le_of_pnat_le H)

theorem inv_gt_of_lt {p q : ℕ+} (H : p < q) : q⁻¹ < p⁻¹ :=
one_div_lt_one_div_of_lt !rat_of_pnat_is_pos (rat_of_pnat_lt_of_pnat_lt H)

theorem ge_of_inv_le {p q : ℕ+} (H : p⁻¹ ≤ q⁻¹) : q ≤ p :=
pnat_le_of_rat_of_pnat_le (le_of_one_div_le_one_div !rat_of_pnat_is_pos H)

theorem two_mul (p : ℕ+) : rat_of_pnat (2 * p) = (1 + 1) * rat_of_pnat p :=
by rewrite pnat_to_rat_mul

theorem add_halves (p : ℕ+) : (2 * p)⁻¹ + (2 * p)⁻¹ = p⁻¹ :=
begin
  rewrite [↑inv, -(add_halves (1 / (rat_of_pnat p))), algebra.div_div_eq_div_mul],
  have H : rat_of_pnat (2 * p) = rat_of_pnat p * (1 + 1), by rewrite [rat.mul.comm, two_mul],
  rewrite *H
end

theorem add_halves_double (m n : ℕ+) :
        m⁻¹ + n⁻¹ = ((2 * m)⁻¹ + (2 * n)⁻¹) + ((2 * m)⁻¹ + (2 * n)⁻¹) :=
have hsimp [visible] : ∀ a b : ℚ, (a + a) + (b + b) = (a + b) + (a + b),
  by intros; rewrite [rat.add.assoc, -(rat.add.assoc a b b), {_+b}rat.add.comm, -*rat.add.assoc],
by rewrite [-add_halves m, -add_halves n, hsimp]

theorem inv_mul_eq_mul_inv {p q : ℕ+} : (p * q)⁻¹ = p⁻¹ * q⁻¹ :=
begin rewrite [↑inv, pnat_to_rat_mul, algebra.one_div_mul_one_div] end

theorem inv_mul_le_inv (p q : ℕ+) : (p * q)⁻¹ ≤ q⁻¹ :=
begin
  rewrite [inv_mul_eq_mul_inv, -{q⁻¹}rat.one_mul at {2}],
  apply algebra.mul_le_mul,
  apply inv_le_one,
  apply rat.le.refl,
  apply rat.le_of_lt,
  apply inv_pos,
  apply rat.le_of_lt rat.zero_lt_one
end

theorem pnat_mul_le_mul_left' (a b c : ℕ+) : a ≤ b → c * a ≤ c * b :=
begin
  rewrite +le.def, intro H,
  apply mul_le_mul_of_nonneg_left H,
  apply algebra.le_of_lt,
  apply pnat_pos
end

theorem mul.assoc (a b c : ℕ+) : a * b * c = a * (b * c) :=
pnat.eq !mul.assoc

theorem mul.comm (a b : ℕ+) : a * b = b * a :=
pnat.eq !mul.comm

theorem add.assoc (a b c : ℕ+) : a + b + c = a + (b + c) :=
pnat.eq !add.assoc

theorem mul_le_mul_left (p q : ℕ+) : q ≤ p * q :=
begin
  rewrite [-one_mul at {1}, mul.comm, mul.comm p],
  apply pnat_mul_le_mul_left',
  apply pone_le
end

theorem mul_le_mul_right (p q : ℕ+) : p ≤ p * q :=
by rewrite mul.comm; apply mul_le_mul_left

theorem pnat.lt_of_not_le {p q : ℕ+} : ¬ p ≤ q → q < p :=
begin rewrite [le.def, lt.def], apply lt_of_not_ge end

theorem inv_cancel_left (p : ℕ+) : rat_of_pnat p * p⁻¹ = (1 : ℚ) :=
mul_one_div_cancel (ne.symm (ne_of_lt !rat_of_pnat_is_pos))

theorem inv_cancel_right (p : ℕ+) : p⁻¹ * rat_of_pnat p = (1 : ℚ) :=
by rewrite rat.mul.comm; apply inv_cancel_left

theorem lt_add_left (p q : ℕ+) : p < p + q :=
begin
  have H : p~ < p~ + q~, begin
    rewrite -nat.add_zero at {1},
    apply nat.add_lt_add_left,
    apply pnat_pos
  end,
  apply H
end

theorem inv_add_lt_left (p q : ℕ+) : (p + q)⁻¹ < p⁻¹ :=
by apply inv_gt_of_lt; apply lt_add_left

theorem div_le_pnat (q : ℚ) (n : ℕ+) (H : q ≥ n⁻¹) : 1 / q ≤ rat_of_pnat n :=
begin
  apply algebra.div_le_of_le_mul,
  apply algebra.lt_of_lt_of_le,
  apply inv_pos,
  rotate 1,
  apply H,
  apply le_mul_of_div_le,
  apply rat_of_pnat_is_pos,
  apply H
end

theorem pnat_cancel' (n m : ℕ+) : (n * n * m)⁻¹ * (rat_of_pnat n * rat_of_pnat n) = m⁻¹ :=
assert hsimp : ∀ a b c : ℚ, (a * a * (b * b * c)) = (a * b) * (a * b) * c,
  begin
    intro a b c,
    rewrite[-*rat.mul.assoc],
    exact (!mul.right_comm ▸ rfl),
  end,
by rewrite [rat.mul.comm, *inv_mul_eq_mul_inv, hsimp, *inv_cancel_left, *rat.one_mul]

definition pceil (a : ℚ) : ℕ+ := tag (ubound a) !ubound_pos

theorem pceil_helper {a : ℚ} {n : ℕ+} (H : pceil a ≤ n) (Ha : a > 0) : n⁻¹ ≤ 1 / a :=
algebra.le.trans (inv_ge_of_le H) (one_div_le_one_div_of_le Ha (ubound_ge a))

theorem inv_pceil_div (a b : ℚ) (Ha : a > 0) (Hb : b > 0) : (pceil (a / b))⁻¹ ≤ b / a :=
assert (pceil (a / b))⁻¹ ≤ 1 / (1 / (b / a)),
  begin
    apply one_div_le_one_div_of_le,
    show 0 < 1 / (b / a), from
      one_div_pos_of_pos (div_pos_of_pos_of_pos Hb Ha),
    show 1 / (b / a) ≤ rat_of_pnat (pceil (a / b)),
    begin
      rewrite div_div_eq_mul_div,
      rewrite algebra.one_mul,
      apply ubound_ge
    end
  end,
begin
  rewrite one_div_one_div at this,
  exact this
end

theorem sep_by_inv {a b : ℚ} : a > b → ∃ N : ℕ+, a > (b + N⁻¹ + N⁻¹) :=
begin
  change b < a → ∃ N : ℕ+, (b + N⁻¹ + N⁻¹) < a,
  intro H,
  apply exists.elim (exists_add_lt_and_pos_of_lt H),
  intro c Hc,
  existsi (pceil ((1 + 1 + 1) / c)),
  apply algebra.lt.trans,
  rotate 1,
  apply and.left Hc,
  rewrite rat.add.assoc,
  apply rat.add_lt_add_left,
  rewrite -(algebra.add_halves c) at {3},
  apply add_lt_add,
  repeat (apply algebra.lt_of_le_of_lt;
    apply inv_pceil_div;
    apply dec_trivial;
    apply and.right Hc;
    apply div_lt_div_of_pos_of_lt_of_pos;
    apply two_pos;
    exact dec_trivial;
    apply and.right Hc)
end

theorem nonneg_of_ge_neg_invs (a : ℚ) : (∀ n : ℕ+, -n⁻¹ ≤ a) → 0 ≤ a :=
begin
  intro H,
  apply algebra.le_of_not_gt,
  suppose a < 0,
  have H2 : 0 < -a, from neg_pos_of_neg this,
  (algebra.not_lt_of_ge !H) (iff.mp !lt_neg_iff_lt_neg (calc
    (pceil (of_num 2 / -a))⁻¹ ≤ -a / of_num 2
        : !inv_pceil_div dec_trivial H2
                           ... < -a / 1
        : div_lt_div_of_pos_of_lt_of_pos dec_trivial dec_trivial H2
                           ... = -a : !div_one))
end

theorem pnat_bound {ε : ℚ} (Hε : ε > 0) : ∃ p : ℕ+, p⁻¹ ≤ ε :=
begin
  existsi (pceil (1 / ε)),
  rewrite -(one_div_one_div ε) at {2},
  apply pceil_helper,
  apply le.refl,
  apply one_div_pos_of_pos Hε
end

theorem p_add_fractions (n : ℕ+) : (2 * n)⁻¹ + (2 * 3 * n)⁻¹ + (3 * n)⁻¹ = n⁻¹ :=
assert T : 2⁻¹ + 2⁻¹ * 3⁻¹ + 3⁻¹ = 1, from dec_trivial,
by rewrite[*inv_mul_eq_mul_inv,-*right_distrib,T,rat.one_mul]

theorem rat_power_two_le (k : ℕ+) : rat_of_pnat k ≤ 2^k~ :=
!binary_nat_bound

end pnat
