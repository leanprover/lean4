/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Adds the ordering, and instantiates the rationals as an ordered field.
-/

import data.int algebra.ordered_field .basic
open quot eq.ops

/- the ordering on representations -/

namespace prerat
section int_notation
open int

variables {a b : prerat}

definition pos (a : prerat) : Prop := num a > 0

definition nonneg (a : prerat) : Prop := num a ≥ 0

theorem pos_of_int (a : ℤ) : pos (of_int a) ↔ (#int a > 0) :=
!iff.rfl

theorem nonneg_of_int (a : ℤ) : nonneg (of_int a) ↔ (#int a ≥ 0) :=
!iff.rfl

theorem pos_eq_pos_of_equiv {a b : prerat} (H1 : a ≡ b) : pos a = pos b :=
propext (iff.intro (num_pos_of_equiv H1) (num_pos_of_equiv H1⁻¹))

theorem nonneg_eq_nonneg_of_equiv (H : a ≡ b) : nonneg a = nonneg b :=
have H1 : (0 = num a) = (0 = num b),
  from propext (iff.intro
    (assume H2, eq.symm (num_eq_zero_of_equiv H H2⁻¹))
    (assume H2, eq.symm (num_eq_zero_of_equiv H⁻¹ H2⁻¹))),
calc
  nonneg a = (pos a ∨ 0 = num a) : propext !le_iff_lt_or_eq
       ... = (pos b ∨ 0 = num a) : pos_eq_pos_of_equiv H
       ... = (pos b ∨ 0 = num b) : H1
       ... = nonneg b            : propext !le_iff_lt_or_eq

theorem nonneg_zero : nonneg zero := le.refl 0

theorem nonneg_add (H1 : nonneg a) (H2 : nonneg b) : nonneg (add a b) :=
show num a * denom b + num b * denom a ≥ 0,
  from add_nonneg
    (mul_nonneg H1 (le_of_lt (denom_pos b)))
    (mul_nonneg H2 (le_of_lt (denom_pos a)))

theorem nonneg_antisymm (H1 : nonneg a) (H2 : nonneg (neg a)) : a ≡ zero :=
have H3 : num a = 0, from le.antisymm (nonpos_of_neg_nonneg H2) H1,
equiv_zero_of_num_eq_zero H3

theorem nonneg_total (a : prerat) : nonneg a ∨ nonneg (neg a) :=
or.elim (le.total 0 (num a))
  (suppose 0 ≤ num a, or.inl this)
  (suppose 0 ≥ num a, or.inr (neg_nonneg_of_nonpos this))

theorem nonneg_of_pos (H : pos a) : nonneg a := le_of_lt H

theorem ne_zero_of_pos (H : pos a) : ¬ a ≡ zero :=
assume H', ne_of_gt H (num_eq_zero_of_equiv_zero H')

theorem pos_of_nonneg_of_ne_zero (H1 : nonneg a) (H2 : ¬ a ≡ zero) : pos a :=
have num a ≠ 0, from suppose num a = 0, H2 (equiv_zero_of_num_eq_zero this),
lt_of_le_of_ne H1 (ne.symm this)

theorem nonneg_mul (H1 : nonneg a) (H2 : nonneg b) : nonneg (mul a b) :=
mul_nonneg H1 H2

theorem pos_mul (H1 : pos a) (H2 : pos b) : pos (mul a b) :=
mul_pos H1 H2

end int_notation
end prerat

local attribute prerat.setoid [instance]

/- The ordering on the rationals.

   The definitions of pos and nonneg are kept private, because they are only meant for internal
   use. Users should use a > 0 and a ≥ 0 instead of pos and nonneg.
-/

namespace rat

variables {a b c : ℚ}

/- transfer properties of pos and nonneg -/

private definition pos (a : ℚ) : Prop :=
quot.lift prerat.pos @prerat.pos_eq_pos_of_equiv a

private definition nonneg (a : ℚ) : Prop :=
quot.lift prerat.nonneg @prerat.nonneg_eq_nonneg_of_equiv a

private theorem pos_of_int (a : ℤ) : (#int a > 0) ↔ pos (of_int a) :=
prerat.pos_of_int a

private theorem nonneg_of_int (a : ℤ) : (#int a ≥ 0) ↔ nonneg (of_int a) :=
prerat.nonneg_of_int a

private theorem nonneg_zero : nonneg 0 := prerat.nonneg_zero

private theorem nonneg_add : nonneg a → nonneg b → nonneg (a + b) :=
quot.induction_on₂ a b @prerat.nonneg_add

private theorem nonneg_antisymm : nonneg a → nonneg (-a) → a = 0 :=
quot.induction_on a
  (take u, assume H1 H2,
    quot.sound (prerat.nonneg_antisymm H1 H2))

private theorem nonneg_total (a : ℚ) : nonneg a ∨ nonneg (-a) :=
quot.induction_on a @prerat.nonneg_total

private theorem nonneg_of_pos : pos a → nonneg a :=
quot.induction_on a @prerat.nonneg_of_pos

private theorem ne_zero_of_pos : pos a → a ≠ 0 :=
quot.induction_on a (take u, assume H1 H2, prerat.ne_zero_of_pos H1 (quot.exact H2))

private theorem pos_of_nonneg_of_ne_zero : nonneg a → ¬ a = 0 → pos a :=
quot.induction_on a
  (take u,
   assume h : nonneg ⟦u⟧,
   suppose ⟦u⟧ ≠ (rat.of_num 0),
   have ¬ (prerat.equiv u prerat.zero), from assume H, this (quot.sound H),
   prerat.pos_of_nonneg_of_ne_zero h this)

private theorem nonneg_mul : nonneg a → nonneg b → nonneg (a * b) :=
quot.induction_on₂ a b @prerat.nonneg_mul

private theorem pos_mul : pos a → pos b → pos (a * b) :=
quot.induction_on₂ a b @prerat.pos_mul

private definition decidable_pos (a : ℚ) : decidable (pos a) :=
quot.rec_on_subsingleton a (take u, int.decidable_lt 0 (prerat.num u))

/- define order in terms of pos and nonneg -/

definition lt (a b : ℚ) : Prop := pos (b - a)
definition le (a b : ℚ) : Prop := nonneg (b - a)
definition gt [reducible] (a b : ℚ) := lt b a
definition ge [reducible] (a b : ℚ) := le b a

infix [priority rat.prio] <  := rat.lt
infix [priority rat.prio] <= := rat.le
infix [priority rat.prio] ≤  := rat.le
infix [priority rat.prio] >= := rat.ge
infix [priority rat.prio] ≥  := rat.ge
infix [priority rat.prio] >  := rat.gt

theorem of_int_lt_of_int (a b : ℤ) : of_int a < of_int b ↔ (#int a < b) :=
iff.symm (calc
  (#int a < b) ↔ (#int b - a > 0)          : iff.symm !int.sub_pos_iff_lt
           ... ↔ pos (of_int (#int b - a)) : iff.symm !pos_of_int
           ... ↔ pos (of_int b - of_int a) : !of_int_sub ▸ iff.rfl
           ... ↔ of_int a < of_int b       : iff.rfl)

theorem of_int_le_of_int (a b : ℤ) : of_int a ≤ of_int b ↔ (#int a ≤ b) :=
iff.symm (calc
  (#int a ≤ b) ↔ (#int b - a ≥ 0)             : iff.symm !int.sub_nonneg_iff_le
           ... ↔ nonneg (of_int (#int b - a)) : iff.symm !nonneg_of_int
           ... ↔ nonneg (of_int b - of_int a) : !of_int_sub ▸ iff.rfl
           ... ↔ of_int a ≤ of_int b          : iff.rfl)

theorem of_int_pos (a : ℤ) : (of_int a > 0) ↔ (#int a > 0) := !of_int_lt_of_int

theorem of_int_nonneg (a : ℤ) : (of_int a ≥ 0) ↔ (#int a ≥ 0) := !of_int_le_of_int

theorem of_nat_lt_of_nat (a b : ℕ) : of_nat a < of_nat b ↔ (#nat a < b) :=
by rewrite [*of_nat_eq, propext !of_int_lt_of_int]; apply int.of_nat_lt_of_nat

theorem of_nat_le_of_nat (a b : ℕ) : of_nat a ≤ of_nat b ↔ (#nat a ≤ b) :=
by rewrite [*of_nat_eq, propext !of_int_le_of_int]; apply int.of_nat_le_of_nat

theorem of_nat_pos (a : ℕ) : (of_nat a > 0) ↔ (#nat a > nat.zero) :=
!of_nat_lt_of_nat

theorem of_nat_nonneg (a : ℕ) : (of_nat a ≥ 0) :=
iff.mpr !of_nat_le_of_nat !nat.zero_le

theorem le.refl (a : ℚ) : a ≤ a :=
by rewrite [↑rat.le, sub_self]; apply nonneg_zero

theorem le.trans (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c :=
assert H3 : nonneg (c - b + (b - a)), from nonneg_add H2 H1,
begin
  revert H3,
  rewrite [↑rat.sub, add.assoc, neg_add_cancel_left],
  intro H3, apply H3
end

theorem le.antisymm (H1 : a ≤ b) (H2 : b ≤ a) : a = b :=
have H3 : nonneg (-(a - b)), from !neg_sub⁻¹ ▸ H1,
have H4 : a - b = 0, from nonneg_antisymm H2 H3,
eq_of_sub_eq_zero H4

theorem le.total (a b : ℚ) : a ≤ b ∨ b ≤ a :=
or.elim (nonneg_total (b - a))
  (assume H, or.inl H)
  (assume H, or.inr (!neg_sub ▸ H))

theorem le.by_cases {P : Prop} (a b : ℚ) (H : a ≤ b → P) (H2 : b ≤ a → P) : P :=
  or.elim (!rat.le.total) H H2

theorem lt_iff_le_and_ne (a b : ℚ) : a < b ↔ a ≤ b ∧ a ≠ b :=
iff.intro
  (assume H : a < b,
    have b - a ≠ 0, from ne_zero_of_pos H,
    have a ≠ b, from ne.symm (assume H', this (H' ▸ !sub_self)),
    and.intro (nonneg_of_pos H) this)
  (assume H : a ≤ b ∧ a ≠ b,
    obtain aleb aneb, from H,
    have b - a ≠ 0, from (assume H', aneb (eq_of_sub_eq_zero H')⁻¹),
    pos_of_nonneg_of_ne_zero aleb this)

theorem le_iff_lt_or_eq (a b : ℚ) : a ≤ b ↔ a < b ∨ a = b :=
iff.intro
  (assume h : a ≤ b,
    decidable.by_cases
      (suppose a = b, or.inr this)
      (suppose a ≠ b, or.inl (iff.mpr !lt_iff_le_and_ne (and.intro h this))))
  (suppose a < b ∨ a = b,
    or.elim this
      (suppose a < b, and.left (iff.mp !lt_iff_le_and_ne this))
      (suppose a = b, this ▸ !le.refl))

theorem to_nonneg : a ≥ 0 → nonneg a :=
by intros; rewrite -sub_zero; eassumption

theorem add_le_add_left (H : a ≤ b) (c : ℚ) : c + a ≤ c + b :=
have c + b - (c + a) = b - a,
  by rewrite [↑sub, neg_add, -add.assoc, add.comm c, add_neg_cancel_right],
show nonneg (c + b - (c + a)), from this⁻¹ ▸ H

theorem mul_nonneg (H1 : a ≥ (0 : ℚ)) (H2 : b ≥ (0 : ℚ)) : a * b ≥ (0 : ℚ) :=
have nonneg (a * b), from nonneg_mul (to_nonneg H1) (to_nonneg H2),
!sub_zero⁻¹ ▸ this

theorem to_pos : a > 0 → pos a :=
by intros; rewrite -sub_zero; eassumption

theorem mul_pos (H1 : a > (0 : ℚ)) (H2 : b > (0 : ℚ)) : a * b > (0 : ℚ) :=
have pos (a * b), from pos_mul (to_pos H1) (to_pos H2),
!sub_zero⁻¹ ▸ this

definition decidable_lt [instance] : decidable_rel rat.lt :=
take a b, decidable_pos (b - a)

theorem le_of_lt  (H : a < b) : a ≤ b := iff.mpr !le_iff_lt_or_eq (or.inl H)

theorem lt_irrefl (a : ℚ) : ¬ a < a :=
take Ha,
  let Hand := (iff.mp !lt_iff_le_and_ne) Ha in
  (and.right Hand) rfl

theorem not_le_of_gt (H : a < b) : ¬ b ≤ a :=
assume Hba,
  let Heq := le.antisymm (le_of_lt H) Hba in
  !lt_irrefl (Heq ▸ H)

theorem lt_of_lt_of_le  (Hab : a < b) (Hbc : b ≤ c) : a < c :=
let Hab' := le_of_lt Hab in
let Hac := le.trans Hab' Hbc in
  (iff.mpr !lt_iff_le_and_ne) (and.intro Hac
    (assume Heq, not_le_of_gt (Heq ▸ Hab) Hbc))

theorem lt_of_le_of_lt  (Hab : a ≤ b) (Hbc : b < c) : a < c :=
let Hbc' := le_of_lt Hbc in
let Hac := le.trans Hab Hbc' in
  (iff.mpr !lt_iff_le_and_ne) (and.intro Hac
    (assume Heq, not_le_of_gt (Heq⁻¹ ▸ Hbc) Hab))

theorem zero_lt_one : (0 : ℚ) < 1 := trivial

theorem add_lt_add_left (H : a < b) (c : ℚ) : c + a < c + b :=
let H' := le_of_lt H in
(iff.mpr (lt_iff_le_and_ne _ _)) (and.intro (add_le_add_left H' _)
                                  (take Heq, let Heq' := add_left_cancel Heq in
                                   !lt_irrefl (Heq' ▸ H)))

section migrate_algebra
  open [classes] algebra

  protected definition discrete_linear_ordered_field [reducible] :
    algebra.discrete_linear_ordered_field rat :=
  ⦃algebra.discrete_linear_ordered_field,
    rat.discrete_field,
    le_refl          := le.refl,
    le_trans         := @le.trans,
    le_antisymm      := @le.antisymm,
    le_total         := @le.total,
    le_of_lt         := @le_of_lt,
    lt_irrefl        := lt_irrefl,
    lt_of_lt_of_le   := @lt_of_lt_of_le,
    lt_of_le_of_lt   := @lt_of_le_of_lt,
    le_iff_lt_or_eq  := @le_iff_lt_or_eq,
    add_le_add_left  := @add_le_add_left,
    mul_nonneg       := @mul_nonneg,
    mul_pos          := @mul_pos,
    decidable_lt     := @decidable_lt,
    zero_lt_one      := zero_lt_one,
    add_lt_add_left  := @add_lt_add_left⦄

  local attribute rat.discrete_linear_ordered_field [trans-instance]
  local attribute rat.discrete_field [instance]

  definition min : ℚ → ℚ → ℚ := algebra.min
  definition max : ℚ → ℚ → ℚ := algebra.max
  definition abs : ℚ → ℚ := algebra.abs
  definition sign : ℚ → ℚ := algebra.sign

  migrate from algebra with rat
    replacing has_le.ge → ge, has_lt.gt → gt, sub → sub, dvd → dvd,
              divide → divide, max → max, min → min, abs → abs, sign → sign

  attribute le.trans lt.trans lt_of_lt_of_le lt_of_le_of_lt ge.trans gt.trans gt_of_gt_of_ge
                   gt_of_ge_of_gt [trans]

end migrate_algebra

theorem rat_of_nat_abs (a : ℤ) : abs (of_int a) = of_nat (int.nat_abs a) :=
assert ∀ n : ℕ, of_int (int.neg_succ_of_nat n) = - of_nat (nat.succ n), from λ n, rfl,
int.induction_on a
  (take b, abs_of_nonneg (!of_nat_nonneg))
  (take b, by rewrite [this, abs_neg, abs_of_nonneg (!of_nat_nonneg)])

definition ubound : ℚ → ℕ := λ a : ℚ, nat.succ (int.nat_abs (num a))

theorem ubound_ge (a : ℚ) : of_nat (ubound a) ≥ a :=
have h : abs a * abs (of_int (denom a)) = abs (of_int (num a)), from
  !abs_mul ▸ !mul_denom ▸ rfl,
assert of_int (denom a) > 0, from (iff.mpr !of_int_pos) !denom_pos,
have 1 ≤ abs (of_int (denom a)), begin
    rewrite (abs_of_pos this),
    apply iff.mpr !of_int_le_of_int,
    apply denom_pos
  end,
have abs a ≤ abs (of_int (num a)), from
  le_of_mul_le_of_ge_one (h ▸ !le.refl) !abs_nonneg this,
calc
    a ≤ abs a                                   : le_abs_self
  ... ≤ abs (of_int (num a))                    : this
  ... ≤ abs (of_int (num a)) + 1                : rat.le_add_of_nonneg_right trivial
  ... = of_nat (int.nat_abs (num a)) + 1        : rat_of_nat_abs
  ... = of_nat (nat.succ (int.nat_abs (num a))) : of_nat_add

theorem ubound_pos (a : ℚ) : nat.gt (ubound a) nat.zero := !nat.succ_pos

end rat
