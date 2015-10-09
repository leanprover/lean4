/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Adds the ordering, and instantiates the rationals as an ordered field.
-/
import data.int algebra.ordered_field algebra.group_power data.rat.basic
open quot eq.ops
open - [notations] algebra

/- the ordering on representations -/

namespace prerat
section int_notation
open int

variables {a b : prerat}

definition pos (a : prerat) : Prop := num a > 0

definition nonneg (a : prerat) : Prop := num a ≥ 0

theorem pos_of_int (a : ℤ) : pos (of_int a) ↔ (a > 0) :=
!iff.rfl

theorem nonneg_of_int (a : ℤ) : nonneg (of_int a) ↔ (a ≥ 0) :=
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
open nat int
variables {a b c : ℚ}

/- transfer properties of pos and nonneg -/

private definition pos (a : ℚ) : Prop :=
quot.lift prerat.pos @prerat.pos_eq_pos_of_equiv a

private definition nonneg (a : ℚ) : Prop :=
quot.lift prerat.nonneg @prerat.nonneg_eq_nonneg_of_equiv a

private theorem pos_of_int (a : ℤ) : (a > 0) ↔ pos (of_int a) :=
prerat.pos_of_int a

private theorem nonneg_of_int (a : ℤ) : (a ≥ 0) ↔ nonneg (of_int a) :=
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

protected definition lt (a b : ℚ) : Prop := pos (b - a)
protected definition le (a b : ℚ) : Prop := nonneg (b - a)

definition rat_has_lt [reducible] [instance] [priority rat.prio] : has_lt rat :=
has_lt.mk rat.lt

definition rat_has_le [reducible] [instance] [priority rat.prio] : has_le rat :=
has_le.mk rat.le

lemma lt.def (a b : ℚ) : (a < b) = pos (b - a) :=
rfl

lemma le.def (a b : ℚ) : (a ≤ b) = nonneg (b - a) :=
rfl

theorem of_int_lt_of_int_iff (a b : ℤ) : of_int a < of_int b ↔ a < b :=
iff.symm (calc
  a < b ↔ b - a > 0                 : iff.symm !sub_pos_iff_lt
    ... ↔ pos (of_int (b - a))      : iff.symm !pos_of_int
    ... ↔ pos (of_int b - of_int a) : !of_int_sub ▸ iff.rfl
    ... ↔ of_int a < of_int b       : iff.rfl)

theorem of_int_lt_of_int_of_lt {a b : ℤ} (H : a < b) : of_int a < of_int b :=
iff.mpr !of_int_lt_of_int_iff H

theorem lt_of_of_int_lt_of_int {a b : ℤ} (H : of_int a < of_int b) : a < b :=
iff.mp !of_int_lt_of_int_iff H

theorem of_int_le_of_int_iff (a b : ℤ) : of_int a ≤ of_int b ↔ (a ≤ b) :=
iff.symm (calc
  a ≤ b ↔ b - a ≥ 0                    : iff.symm !sub_nonneg_iff_le
    ... ↔ nonneg (of_int (b - a))      : iff.symm !nonneg_of_int
    ... ↔ nonneg (of_int b - of_int a) : !of_int_sub ▸ iff.rfl
    ... ↔ of_int a ≤ of_int b          : iff.rfl)

theorem of_int_le_of_int_of_le {a b : ℤ} (H : a ≤ b) : of_int a ≤ of_int b :=
iff.mpr !of_int_le_of_int_iff H

theorem le_of_of_int_le_of_int {a b : ℤ} (H : of_int a ≤ of_int b) : a ≤ b :=
iff.mp !of_int_le_of_int_iff H

theorem of_nat_lt_of_nat_iff (a b : ℕ) : of_nat a < of_nat b ↔ a < b :=
by rewrite [*of_nat_eq, of_int_lt_of_int_iff, int.of_nat_lt_of_nat_iff]

theorem of_nat_lt_of_nat_of_lt {a b : ℕ} (H : a < b) : of_nat a < of_nat b :=
iff.mpr !of_nat_lt_of_nat_iff H

theorem lt_of_of_nat_lt_of_nat {a b : ℕ} (H : of_nat a < of_nat b) : a < b :=
iff.mp !of_nat_lt_of_nat_iff H

theorem of_nat_le_of_nat_iff (a b : ℕ) : of_nat a ≤ of_nat b ↔ a ≤ b :=
by rewrite [*of_nat_eq, of_int_le_of_int_iff, int.of_nat_le_of_nat_iff]

theorem of_nat_le_of_nat_of_le {a b : ℕ} (H : a ≤ b) : of_nat a ≤ of_nat b :=
iff.mpr !of_nat_le_of_nat_iff H

theorem le_of_of_nat_le_of_nat {a b : ℕ} (H : of_nat a ≤ of_nat b) : a ≤ b :=
iff.mp !of_nat_le_of_nat_iff H

theorem of_nat_nonneg (a : ℕ) : (of_nat a ≥ 0) :=
of_nat_le_of_nat_of_le !nat.zero_le

theorem le.refl (a : ℚ) : a ≤ a :=
by rewrite [le.def, sub_self]; apply nonneg_zero

theorem le.trans (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c :=
assert H3 : nonneg (c - b + (b - a)), from nonneg_add H2 H1,
begin
  revert H3,
  krewrite [rat.sub.def, add.assoc, neg_add_cancel_left],
  intro H3, apply H3
end

theorem le.antisymm (H1 : a ≤ b) (H2 : b ≤ a) : a = b :=
have H3 : nonneg (-(a - b)), from !neg_sub⁻¹ ▸ H1,
have H4 : a - b = 0, from nonneg_antisymm H2 H3,
eq_of_sub_eq_zero H4

theorem le.total (a b : ℚ) : a ≤ b ∨ b ≤ a :=
or.elim (nonneg_total (b - a))
  (assume H, or.inl H)
  (assume H, or.inr begin rewrite neg_sub at H, exact H end)

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

private theorem to_nonneg : a ≥ 0 → nonneg a :=
by intros; rewrite -sub_zero; eassumption

theorem add_le_add_left (H : a ≤ b) (c : ℚ) : c + a ≤ c + b :=
have c + b - (c + a) = b - a,
  by rewrite [sub.def, neg_add, -add.assoc, add.comm c, add_neg_cancel_right],
show nonneg (c + b - (c + a)), from this⁻¹ ▸ H

theorem mul_nonneg (H1 : a ≥ (0 : ℚ)) (H2 : b ≥ (0 : ℚ)) : a * b ≥ (0 : ℚ) :=
assert nonneg (a * b), from nonneg_mul (to_nonneg H1) (to_nonneg H2),
begin rewrite -sub_zero at this, exact this end

private theorem to_pos : a > 0 → pos a :=
by intros; rewrite -sub_zero; eassumption

theorem mul_pos (H1 : a > (0 : ℚ)) (H2 : b > (0 : ℚ)) : a * b > (0 : ℚ) :=
assert pos (a * b), from pos_mul (to_pos H1) (to_pos H2),
begin rewrite -sub_zero at this, exact this end

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

protected definition discrete_linear_ordered_field [reducible] [trans_instance] :
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

theorem of_nat_abs (a : ℤ) : abs (of_int a) = of_nat (int.nat_abs a) :=
assert ∀ n : ℕ, of_int (int.neg_succ_of_nat n) = - of_nat (nat.succ n), from λ n, rfl,
int.induction_on a
  (take b, abs_of_nonneg !of_nat_nonneg)
  (take b, by rewrite [this, abs_neg, abs_of_nonneg !of_nat_nonneg])

theorem eq_zero_of_nonneg_of_forall_lt {x : ℚ} (xnonneg : x ≥ 0) (H : ∀ ε, ε > 0 → x < ε) :
  x = 0 :=
  decidable.by_contradiction
    (suppose x ≠ 0,
      have x > 0, from lt_of_le_of_ne xnonneg (ne.symm this),
      have x < x, from H x this,
      show false, from !lt.irrefl this)

theorem eq_zero_of_nonneg_of_forall_le {x : ℚ} (xnonneg : x ≥ 0) (H : ∀ ε, ε > 0 → x ≤ ε) :
  x = 0 :=
have H' : ∀ ε, ε > 0 → x < ε, from
  take ε, suppose h₁ : ε > 0,
  have ε / 2 > 0, from div_pos_of_pos_of_pos h₁ two_pos,
  have x ≤ ε / 2, from H _ this,
  show x < ε, from lt_of_le_of_lt this (div_two_lt_of_pos h₁),
eq_zero_of_nonneg_of_forall_lt xnonneg H'

theorem eq_zero_of_forall_abs_le {x : ℚ} (H : ∀ ε, ε > 0 → abs x ≤ ε) :
  x = 0 :=
decidable.by_contradiction
  (suppose x ≠ 0,
    have abs x = 0, from eq_zero_of_nonneg_of_forall_le !abs_nonneg H,
    show false, from `x ≠ 0` (eq_zero_of_abs_eq_zero this))

theorem eq_of_forall_abs_sub_le {x y : ℚ} (H : ∀ ε, ε > 0 → abs (x - y) ≤ ε) :
  x = y :=
have x - y = 0, from eq_zero_of_forall_abs_le H,
eq_of_sub_eq_zero this

section
  open int

  theorem num_nonneg_of_nonneg {q : ℚ} (H : q ≥ 0) : num q ≥ 0 :=
  have of_int (num q) ≥ of_int 0,
    begin
      rewrite [-mul_denom],
      apply mul_nonneg H,
      rewrite [of_int_le_of_int_iff],
      exact int.le_of_lt !denom_pos
    end,
  show num q ≥ 0, from le_of_of_int_le_of_int this

  theorem num_pos_of_pos {q : ℚ} (H : q > 0) : num q > 0 :=
  have of_int (num q) > of_int 0,
    begin
      rewrite [-mul_denom],
      apply mul_pos H,
      rewrite [of_int_lt_of_int_iff],
      exact !denom_pos
    end,
  show num q > 0, from lt_of_of_int_lt_of_int this

  theorem num_neg_of_neg {q : ℚ} (H : q < 0) : num q < 0 :=
  have of_int (num q) < of_int 0,
    begin
      rewrite [-mul_denom],
      apply mul_neg_of_neg_of_pos H,
      change of_int (denom q) > of_int 0,
      xrewrite [of_int_lt_of_int_iff],
      exact !denom_pos
    end,
  show num q < 0, from lt_of_of_int_lt_of_int this

  theorem num_nonpos_of_nonpos {q : ℚ} (H : q ≤ 0) : num q ≤ 0 :=
  have of_int (num q) ≤ of_int 0,
    begin
      rewrite [-mul_denom],
      apply mul_nonpos_of_nonpos_of_nonneg H,
      change of_int (denom q) ≥ of_int 0,
      xrewrite [of_int_le_of_int_iff],
      exact int.le_of_lt !denom_pos
    end,
  show num q ≤ 0, from le_of_of_int_le_of_int this
end

definition ubound : ℚ → ℕ := λ a : ℚ, nat.succ (int.nat_abs (num a))

theorem ubound_ge (a : ℚ) : of_nat (ubound a) ≥ a :=
have h : abs a * abs (of_int (denom a)) = abs (of_int (num a)), from
  !abs_mul ▸ !mul_denom ▸ rfl,
assert of_int (denom a) > 0, from of_int_lt_of_int_of_lt !denom_pos,
have 1 ≤ abs (of_int (denom a)), begin
    rewrite (abs_of_pos this),
    apply of_int_le_of_int_of_le,
    apply denom_pos
  end,
have abs a ≤ abs (of_int (num a)), from
  le_of_mul_le_of_ge_one (h ▸ !le.refl) !abs_nonneg this,
calc
    a ≤ abs a                                   : le_abs_self
  ... ≤ abs (of_int (num a))                    : this
  ... ≤ abs (of_int (num a)) + 1                : le_add_of_nonneg_right trivial
  ... = of_nat (int.nat_abs (num a)) + 1        : of_nat_abs
  ... = of_nat (nat.succ (int.nat_abs (num a))) : of_nat_add

theorem ubound_pos (a : ℚ) : ubound a > 0 :=
!nat.succ_pos

open nat

theorem binary_nat_bound (a : ℕ) : of_nat a ≤ 2^a :=
  nat.induction_on a (zero_le_one)
   (take n : nat, assume Hn,
    calc
     of_nat (nat.succ n) = (of_nat n) + 1 : of_nat_add
       ... ≤ 2^n + 1           : algebra.add_le_add_right Hn
       ... ≤ 2^n + (2:rat)^n   : add_le_add_left (pow_ge_one_of_ge_one two_ge_one _)
       ... = 2^(succ n)        : pow_two_add)

theorem binary_bound (a : ℚ) : ∃ n : ℕ, a ≤ 2^n :=
  exists.intro (ubound a) (calc
      a ≤ of_nat (ubound a) : ubound_ge
    ... ≤ 2^(ubound a) : binary_nat_bound)

end rat
