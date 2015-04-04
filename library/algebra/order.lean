/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.order
Author: Jeremy Avigad

Various types of orders. We develop weak orders "≤" and strict orders "<" separately. We also
consider structures with both, where the two are related by

  x < y ↔ (x ≤ y ∧ x ≠ y)   (order_pair)
  x ≤ y ↔ (x < y ∨ x = y)   (strong_order_pair)

These might not hold constructively in some applications, but we can define additional structures
with both < and ≤ as needed.
-/

import logic.eq logic.connectives
open eq eq.ops

namespace algebra

variable {A : Type}

/- overloaded symbols -/

structure has_le [class] (A : Type) :=
(le : A → A → Prop)

structure has_lt [class] (A : Type) :=
(lt : A → A → Prop)

infixl `<=`   := has_le.le
infixl `≤`   := has_le.le
infixl `<`   := has_lt.lt

definition has_le.ge [reducible] {A : Type} [s : has_le A] (a b : A) := b ≤ a
notation a ≥ b := has_le.ge a b
notation a >= b := has_le.ge a b

definition has_lt.gt [reducible] {A : Type} [s : has_lt A] (a b : A) := b < a
notation a > b := has_lt.gt a b

/- weak orders -/

structure weak_order [class] (A : Type) extends has_le A :=
(le_refl : ∀a, le a a)
(le_trans : ∀a b c, le a b → le b c → le a c)
(le_antisymm : ∀a b, le a b → le b a → a = b)

section
  variable [s : weak_order A]
  include s

  theorem le.refl (a : A) : a ≤ a := !weak_order.le_refl

  theorem le.trans {a b c : A} : a ≤ b → b ≤ c → a ≤ c := !weak_order.le_trans
  calc_trans le.trans

  theorem ge.trans {a b c : A} (H1 : a ≥ b) (H2: b ≥ c) : a ≥ c := le.trans H2 H1
  calc_trans ge.trans

  theorem le.antisymm {a b : A} : a ≤ b → b ≤ a → a = b := !weak_order.le_antisymm
end

structure linear_weak_order [class] (A : Type) extends weak_order A :=
(le_total : ∀a b, le a b ∨ le b a)

theorem le.total [s : linear_weak_order A] (a b : A) : a ≤ b ∨ b ≤ a :=
!linear_weak_order.le_total

/- strict orders -/

structure strict_order [class] (A : Type) extends has_lt A :=
(lt_irrefl : ∀a, ¬ lt a a)
(lt_trans : ∀a b c, lt a b → lt b c → lt a c)

section
  variable [s : strict_order A]
  include s

  theorem lt.irrefl (a : A) : ¬ a < a := !strict_order.lt_irrefl

  theorem lt.trans {a b c : A} : a < b → b < c → a < c := !strict_order.lt_trans
  calc_trans lt.trans

  theorem gt.trans {a b c : A} (H1 : a > b) (H2: b > c) : a > c := lt.trans H2 H1
  calc_trans gt.trans

  theorem ne_of_lt {a b : A} : a < b → a ≠ b :=
  assume lt_ab : a < b, assume eq_ab : a = b,
  show false, from lt.irrefl b (eq_ab ▸ lt_ab)

  theorem lt.asymm {a b : A} (H : a < b) : ¬ b < a :=
  assume H1 : b < a, lt.irrefl _ (lt.trans H H1)
end

/- well-founded orders -/

-- TODO: do these duplicate what Leo has done? if so, eliminate

structure wf_strict_order [class] (A : Type) extends strict_order A :=
(wf_rec : ∀P : A → Type, (∀x, (∀y, lt y x → P y) → P x) → ∀x, P x)

definition wf.rec_on {A : Type} [s : wf_strict_order A] {P : A → Type}
    (x : A) (H : ∀x, (∀y, wf_strict_order.lt y x → P y) → P x) : P x :=
wf_strict_order.wf_rec P H x

theorem wf.ind_on.{u v} {A : Type.{u}} [s : wf_strict_order.{u 0} A] {P : A → Prop}
    (x : A) (H : ∀x, (∀y, wf_strict_order.lt y x → P y) → P x) : P x :=
wf.rec_on x H

/- structures with a weak and a strict order -/

structure order_pair [class] (A : Type) extends weak_order A, has_lt A :=
(lt_iff_le_ne : ∀a b, lt a b ↔ (le a b ∧ a ≠ b))

section
  variable [s : order_pair A]
  variables {a b c : A}
  include s

  theorem lt_iff_le_and_ne : a < b ↔ (a ≤ b ∧ a ≠ b) :=
  !order_pair.lt_iff_le_ne

  theorem le_of_lt (H : a < b) : a ≤ b :=
  and.elim_left (iff.mp lt_iff_le_and_ne H)

  theorem lt_of_le_of_ne (H1 : a ≤ b) (H2 : a ≠ b) : a < b :=
  iff.mp (iff.symm lt_iff_le_and_ne) (and.intro H1 H2)

  private theorem lt_irrefl (s' : order_pair A) (a : A) : ¬ a < a :=
  assume H : a < a,
  have H1 : a ≠ a, from and.elim_right (iff.mp !lt_iff_le_and_ne H),
  H1 rfl

  private theorem lt_trans (s' : order_pair A) (a b c: A) (lt_ab : a < b) (lt_bc : b < c) : a < c :=
  have le_ab : a ≤ b, from le_of_lt lt_ab,
  have le_bc : b ≤ c, from le_of_lt lt_bc,
  have le_ac : a ≤ c, from le.trans le_ab le_bc,
  have ne_ac : a ≠ c, from
    assume eq_ac : a = c,
      have le_ba : b ≤ a, from eq_ac⁻¹ ▸ le_bc,
      have eq_ab : a = b, from le.antisymm le_ab le_ba,
      have ne_ab : a ≠ b, from and.elim_right (iff.mp lt_iff_le_and_ne lt_ab),
      ne_ab eq_ab,
  show a < c, from lt_of_le_of_ne le_ac ne_ac

  definition order_pair.to_strict_order [instance] [coercion] [reducible] : strict_order A :=
  ⦃ strict_order, s, lt_irrefl := lt_irrefl s, lt_trans := lt_trans s ⦄

  theorem lt_of_lt_of_le : a < b → b ≤ c → a < c :=
  assume lt_ab : a < b,
  assume le_bc : b ≤ c,
  have le_ac : a ≤ c, from le.trans (le_of_lt lt_ab) le_bc,
  have ne_ac : a ≠ c, from
    assume eq_ac : a = c,
    have le_ba : b ≤ a, from eq_ac⁻¹ ▸ le_bc,
    have eq_ab : a = b, from le.antisymm (le_of_lt lt_ab) le_ba,
    show false, from ne_of_lt lt_ab eq_ab,
  show a < c, from lt_of_le_of_ne le_ac ne_ac

  theorem lt_of_le_of_lt : a ≤ b → b < c → a < c :=
  assume le_ab : a ≤ b,
  assume lt_bc : b < c,
  have le_ac : a ≤ c, from le.trans le_ab (le_of_lt lt_bc),
  have ne_ac : a ≠ c, from
    assume eq_ac : a = c,
    have le_cb : c ≤ b, from eq_ac ▸ le_ab,
    have eq_bc : b = c, from le.antisymm (le_of_lt lt_bc) le_cb,
    show false, from ne_of_lt lt_bc eq_bc,
  show a < c, from lt_of_le_of_ne le_ac ne_ac

  theorem gt_of_gt_of_ge (H1 : a > b) (H2 : b ≥ c) : a > c := lt_of_le_of_lt H2 H1

  theorem gt_of_ge_of_gt (H1 : a ≥ b) (H2 : b > c) : a > c := lt_of_lt_of_le H2 H1

  calc_trans lt_of_lt_of_le
  calc_trans lt_of_le_of_lt
  calc_trans gt_of_gt_of_ge
  calc_trans gt_of_ge_of_gt

  theorem not_le_of_lt (H : a < b) : ¬ b ≤ a :=
  assume H1 : b ≤ a,
  lt.irrefl _ (lt_of_lt_of_le H H1)

  theorem not_lt_of_le (H : a ≤ b) : ¬ b < a :=
  assume H1 : b < a,
  lt.irrefl _ (lt_of_le_of_lt H H1)
end

structure strong_order_pair [class] (A : Type) extends order_pair A :=
(le_iff_lt_or_eq : ∀a b, le a b ↔ lt a b ∨ a = b)

theorem le_iff_lt_or_eq [s : strong_order_pair A] {a b : A} : a ≤ b ↔ a < b ∨ a = b :=
!strong_order_pair.le_iff_lt_or_eq

theorem lt_or_eq_of_le [s : strong_order_pair A] {a b : A} (le_ab : a ≤ b) : a < b ∨ a = b :=
iff.mp le_iff_lt_or_eq le_ab

-- We can also construct a strong order pair by defining a strict order, and then defining
-- x ≤ y ↔ x < y ∨ x = y

structure strict_order_with_le [class] (A : Type) extends strict_order A, has_le A :=
(le_iff_lt_or_eq : ∀a b, le a b ↔ lt a b ∨ a = b)

private theorem le_refl (s : strict_order_with_le A) (a : A) : a ≤ a :=
iff.mp (iff.symm !strict_order_with_le.le_iff_lt_or_eq) (or.intro_right _ rfl)

private theorem le_trans (s : strict_order_with_le A) (a b c : A) (le_ab : a ≤ b) (le_bc : b ≤ c) : a ≤ c :=
or.elim (iff.mp !strict_order_with_le.le_iff_lt_or_eq le_ab)
  (assume lt_ab : a < b,
    or.elim (iff.mp !strict_order_with_le.le_iff_lt_or_eq le_bc)
      (assume lt_bc : b < c,
        iff.elim_right
          !strict_order_with_le.le_iff_lt_or_eq (or.intro_left _ (lt.trans lt_ab lt_bc)))
      (assume eq_bc : b = c, eq_bc ▸ le_ab))
  (assume eq_ab : a = b,
    eq_ab⁻¹ ▸ le_bc)

private theorem le_antisymm (s : strict_order_with_le A) (a b : A) (le_ab : a ≤ b) (le_ba : b ≤ a) : a = b :=
or.elim (iff.mp !strict_order_with_le.le_iff_lt_or_eq le_ab)
  (assume lt_ab : a < b,
    or.elim (iff.mp !strict_order_with_le.le_iff_lt_or_eq le_ba)
      (assume lt_ba : b < a, absurd (lt.trans lt_ab lt_ba) (lt.irrefl a))
      (assume eq_ba : b = a, eq_ba⁻¹))
  (assume eq_ab : a = b, eq_ab)

private theorem lt_iff_le_ne (s : strict_order_with_le A) (a b : A) : a < b ↔ a ≤ b ∧ a ≠ b :=
iff.intro
  (assume lt_ab : a < b,
    have le_ab : a ≤ b, from
      iff.elim_right !strict_order_with_le.le_iff_lt_or_eq (or.intro_left _ lt_ab),
    show a ≤ b ∧ a ≠ b, from and.intro le_ab (ne_of_lt lt_ab))
  (assume H : a ≤ b ∧ a ≠ b,
    have H1 : a < b ∨ a = b, from
      iff.mp !strict_order_with_le.le_iff_lt_or_eq (and.elim_left H),
    show a < b, from or_resolve_left H1 (and.elim_right H))

definition strict_order_with_le.to_order_pair [instance] [coercion] [reducible] [s : strict_order_with_le A] :
  strong_order_pair A :=
⦃ strong_order_pair, s,
  le_refl      := le_refl s,
  le_trans     := le_trans s,
  le_antisymm  := le_antisymm s,
  lt_iff_le_ne := lt_iff_le_ne s ⦄

/- linear orders -/

structure linear_order_pair [class] (A : Type) extends order_pair A, linear_weak_order A

structure linear_strong_order_pair [class] (A : Type) extends strong_order_pair A,
    linear_weak_order A

section
  variable [s : linear_strong_order_pair A]
  variables (a b c : A)
  include s

  theorem lt.trichotomy : a < b ∨ a = b ∨ b < a :=
  or.elim (le.total a b)
    (assume H : a ≤ b,
      or.elim (iff.mp !le_iff_lt_or_eq H) (assume H1, or.inl H1) (assume H1, or.inr (or.inl H1)))
    (assume H : b ≤ a,
      or.elim (iff.mp !le_iff_lt_or_eq H)
        (assume H1, or.inr (or.inr H1))
        (assume H1, or.inr (or.inl (H1⁻¹))))

  theorem lt.by_cases {a b : A} {P : Prop}
    (H1 : a < b → P) (H2 : a = b → P) (H3 : b < a → P) : P :=
  or.elim !lt.trichotomy
    (assume H, H1 H)
    (assume H, or.elim H (assume H', H2 H') (assume H', H3 H'))

  definition linear_strong_order_pair.to_linear_order_pair [instance] [coercion] [reducible]
     : linear_order_pair A :=
  ⦃ linear_order_pair, s ⦄

  theorem le_of_not_lt {a b : A} (H : ¬ a < b) : b ≤ a :=
  lt.by_cases (assume H', absurd H' H) (assume H', H' ▸ !le.refl) (assume H', le_of_lt H')

  theorem lt_of_not_le {a b : A} (H : ¬ a ≤ b) : b < a :=
  lt.by_cases
    (assume H', absurd (le_of_lt H') H)
    (assume H', absurd (H' ▸ !le.refl) H)
    (assume H', H')

  theorem lt_or_ge : a < b ∨ a ≥ b :=
  lt.by_cases
    (assume H1 : a < b, or.inl H1)
    (assume H1 : a = b, or.inr (H1 ▸ le.refl a))
    (assume H1 : a > b, or.inr (le_of_lt H1))

  theorem le_or_gt : a ≤ b ∨ a > b :=
  !or.swap (lt_or_ge b a)

  theorem lt_or_gt_of_ne {a b : A} (H : a ≠ b) : a < b ∨ a > b :=
  lt.by_cases (assume H1, or.inl H1) (assume H1, absurd H1 H) (assume H1, or.inr H1)
end

structure decidable_linear_order [class] (A : Type) extends linear_strong_order_pair A :=
(decidable_lt : decidable_rel lt)

section
  variable [s : decidable_linear_order A]
  variables {a b c d : A}
  include s
  open decidable

  definition decidable_lt [instance] : decidable (a < b) :=
    @decidable_linear_order.decidable_lt _ _ _ _

  definition decidable_le [instance] : decidable (a ≤ b) :=
  by_cases
    (assume H : a < b, inl (le_of_lt H))
    (assume H : ¬ a < b,
      have H1 : b ≤ a, from le_of_not_lt H,
      by_cases
        (assume H2 : b < a, inr (not_le_of_lt H2))
        (assume H2 : ¬ b < a, inl (le_of_not_lt H2)))

  definition decidable_eq [instance] : decidable (a = b) :=
  by_cases
    (assume H : a ≤ b,
      by_cases
        (assume H1 : b ≤ a, inl (le.antisymm H H1))
        (assume H1 : ¬ b ≤ a, inr (assume H2 : a = b, H1 (H2 ▸ le.refl a))))
    (assume H : ¬ a ≤ b,
      (inr (assume H1 : a = b, H (H1 ▸ !le.refl))))

  -- testing equality first may result in more definitional equalities
  definition lt.cases {B : Type} (a b : A) (t_lt t_eq t_gt : B) : B :=
  if a = b then t_eq else (if a < b then t_lt else t_gt)

  theorem lt.cases_of_eq {B : Type} {a b : A} {t_lt t_eq t_gt : B} (H : a = b) :
    lt.cases a b t_lt t_eq t_gt = t_eq := if_pos H

  theorem lt.cases_of_lt {B : Type} {a b : A} {t_lt t_eq t_gt : B} (H : a < b) :
    lt.cases a b t_lt t_eq t_gt = t_lt :=
  if_neg (ne_of_lt H) ⬝ if_pos H

  theorem lt.cases_of_gt {B : Type} {a b : A} {t_lt t_eq t_gt : B} (H : a > b) :
    lt.cases a b t_lt t_eq t_gt = t_gt :=
  if_neg (ne.symm (ne_of_lt H)) ⬝ if_neg (lt.asymm H)
end

end algebra

/-
For reference, these are all the transitivity rules defined in this file:
calc_trans le.trans
calc_trans lt.trans

calc_trans lt_of_lt_of_le
calc_trans lt_of_le_of_lt

calc_trans ge.trans
calc_trans gt.trans

calc_trans gt_of_gt_of_ge
calc_trans gt_of_ge_of_gt
-/
