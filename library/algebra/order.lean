/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Weak orders "≤", strict orders "<", and structures that include both.
-/
import logic.eq logic.connectives algebra.binary algebra.priority
open eq eq.ops

namespace algebra

variable {A : Type}

/- overloaded symbols -/

structure has_le [class] (A : Type) :=
(le : A → A → Prop)

structure has_lt [class] (A : Type) :=
(lt : A → A → Prop)

infixl [priority algebra.prio] `<=`  := has_le.le
infixl [priority algebra.prio] `≤`   := has_le.le
infixl [priority algebra.prio] `<`   := has_lt.lt

definition has_le.ge [reducible] {A : Type} [s : has_le A] (a b : A) := b ≤ a
notation [priority algebra.prio] a ≥ b := has_le.ge a b
notation [priority algebra.prio] a >= b := has_le.ge a b

definition has_lt.gt [reducible] {A : Type} [s : has_lt A] (a b : A) := b < a
notation [priority algebra.prio] a > b := has_lt.gt a b

/- weak orders -/

structure weak_order [class] (A : Type) extends has_le A :=
(le_refl : ∀a, le a a)
(le_trans : ∀a b c, le a b → le b c → le a c)
(le_antisymm : ∀a b, le a b → le b a → a = b)

section
  variable [s : weak_order A]
  include s

  theorem le.refl (a : A) : a ≤ a := !weak_order.le_refl

  theorem le.trans [trans] {a b c : A} : a ≤ b → b ≤ c → a ≤ c := !weak_order.le_trans

  theorem ge.trans [trans] {a b c : A} (H1 : a ≥ b) (H2: b ≥ c) : a ≥ c := le.trans H2 H1

  theorem le.antisymm {a b : A} : a ≤ b → b ≤ a → a = b := !weak_order.le_antisymm

  -- Alternate syntax. (Abbreviations do not migrate well.)
  theorem eq_of_le_of_ge {a b : A} : a ≤ b → b ≤ a → a = b := !le.antisymm
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
  theorem not_lt_self (a : A) : ¬ a < a := !lt.irrefl   -- alternate syntax

  theorem lt.trans [trans] {a b c : A} : a < b → b < c → a < c := !strict_order.lt_trans

  theorem gt.trans [trans] {a b c : A} (H1 : a > b) (H2: b > c) : a > c := lt.trans H2 H1

  theorem ne_of_lt {a b : A} (lt_ab : a < b) : a ≠ b :=
  assume eq_ab : a = b,
  show false, from lt.irrefl b (eq_ab ▸ lt_ab)

  theorem ne_of_gt {a b : A} (gt_ab : a > b) : a ≠ b :=
  ne.symm (ne_of_lt gt_ab)

  theorem lt.asymm {a b : A} (H : a < b) : ¬ b < a :=
  assume H1 : b < a, lt.irrefl _ (lt.trans H H1)

  theorem not_lt_of_gt {a b : A} (H : a > b) : ¬ a < b := !lt.asymm H    -- alternate syntax
end

/- well-founded orders -/

structure wf_strict_order [class] (A : Type) extends strict_order A :=
(wf_rec : ∀P : A → Type, (∀x, (∀y, lt y x → P y) → P x) → ∀x, P x)

definition wf.rec_on {A : Type} [s : wf_strict_order A] {P : A → Type}
    (x : A) (H : ∀x, (∀y, wf_strict_order.lt y x → P y) → P x) : P x :=
wf_strict_order.wf_rec P H x

theorem wf.ind_on.{u v} {A : Type.{u}} [s : wf_strict_order.{u 0} A] {P : A → Prop}
    (x : A) (H : ∀x, (∀y, wf_strict_order.lt y x → P y) → P x) : P x :=
wf.rec_on x H

/- lattices (we could split this to upper- and lower-semilattices, if needed) -/

structure lattice [class] (A : Type) extends weak_order A :=
(min : A → A → A)
(max : A → A → A)
(min_le_left : ∀ a b, le (min a b) a)
(min_le_right : ∀ a b, le (min a b) b)
(le_min : ∀a b c, le c a → le c b → le c (min a b))
(le_max_left : ∀ a b, le a (max a b))
(le_max_right : ∀ a b, le b (max a b))
(max_le : ∀ a b c, le a c → le b c → le (max a b) c)

definition min := @lattice.min
definition max := @lattice.max

section
  variable [s : lattice A]
  include s

  theorem min_le_left (a b : A) : min a b ≤ a := !lattice.min_le_left

  theorem min_le_right (a b : A) : min a b ≤ b := !lattice.min_le_right

  theorem le_min {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) : c ≤ min a b := !lattice.le_min H₁ H₂

  theorem le_max_left (a b : A) : a ≤ max a b := !lattice.le_max_left

  theorem le_max_right (a b : A) : b ≤ max a b := !lattice.le_max_right

  theorem max_le {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) : max a b ≤ c := !lattice.max_le H₁ H₂

  /- min -/

  theorem eq_min {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) (H₃ : ∀{d}, d ≤ a → d ≤ b → d ≤ c) :
    c = min a b :=
  le.antisymm (le_min H₁ H₂) (H₃ !min_le_left !min_le_right)

  theorem min.comm (a b : A) : min a b = min b a :=
  eq_min !min_le_right !min_le_left (λ c H₁ H₂, le_min H₂ H₁)

  theorem min.assoc (a b c : A) : min (min a b) c = min a (min b c) :=
  begin
    apply eq_min,
    { apply le.trans, apply min_le_left, apply min_le_left },
    { apply le_min, apply le.trans, apply min_le_left, apply min_le_right, apply min_le_right },
    { intros [d, H₁, H₂], apply le_min, apply le_min H₁, apply le.trans H₂, apply min_le_left,
      apply le.trans H₂, apply min_le_right }
  end

  theorem min.left_comm (a b c : A) : min a (min b c) = min b (min a c) :=
  binary.left_comm (@min.comm A s) (@min.assoc A s) a b c

  theorem min.right_comm (a b c : A) : min (min a b) c = min (min a c) b :=
  binary.right_comm (@min.comm A s) (@min.assoc A s) a b c

  theorem min_self (a : A) : min a a = a :=
  by apply eq.symm; apply eq_min (le.refl a) !le.refl; intros; assumption

  theorem min_eq_left {a b : A} (H : a ≤ b) : min a b = a :=
  by apply eq.symm; apply eq_min !le.refl H; intros; assumption

  theorem min_eq_right {a b : A} (H : b ≤ a) : min a b = b :=
  eq.subst !min.comm (min_eq_left H)

  /- max -/

  theorem eq_max {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) (H₃ : ∀{d}, a ≤ d → b ≤ d → c ≤ d) :
    c = max a b :=
  le.antisymm (H₃ !le_max_left !le_max_right) (max_le H₁ H₂)

  theorem max.comm (a b : A) : max a b = max b a :=
  eq_max !le_max_right !le_max_left (λ c H₁ H₂, max_le H₂ H₁)

  theorem max.assoc (a b c : A) : max (max a b) c = max a (max b c) :=
  begin
    apply eq_max,
    { apply le.trans, apply le_max_left a b, apply le_max_left },
    { apply max_le, apply le.trans, apply le_max_right a b, apply le_max_left, apply le_max_right },
    { intros [d, H₁, H₂], apply max_le, apply max_le H₁, apply le.trans !le_max_left H₂,
      apply le.trans !le_max_right H₂}
  end

  theorem max.left_comm (a b c : A) : max a (max b c) = max b (max a c) :=
  binary.left_comm (@max.comm A s) (@max.assoc A s) a b c

  theorem max.right_comm (a b c : A) : max (max a b) c = max (max a c) b :=
  binary.right_comm (@max.comm A s) (@max.assoc A s) a b c

  theorem max_self (a : A) : max a a = a :=
  by apply eq.symm; apply eq_max (le.refl a) !le.refl; intros; assumption

  theorem max_eq_left {a b : A} (H : b ≤ a) : max a b = a :=
  by apply eq.symm; apply eq_max !le.refl H; intros; assumption

  theorem max_eq_right {a b : A} (H : a ≤ b) : max a b = b :=
  eq.subst !max.comm (max_eq_left H)
end

/- structures with a weak and a strict order -/

structure order_pair [class] (A : Type) extends weak_order A, has_lt A :=
(le_of_lt : ∀ a b, lt a b → le a b)
(lt_of_lt_of_le : ∀ a b c, lt a b → le b c → lt a c)
(lt_of_le_of_lt : ∀ a b c, le a b → lt b c → lt a c)
(lt_irrefl : ∀ a, ¬ lt a a)

section
  variable [s : order_pair A]
  variables {a b c : A}
  include s

  theorem le_of_lt : a < b → a ≤ b := !order_pair.le_of_lt

  theorem lt_of_lt_of_le [trans] : a < b → b ≤ c → a < c := !order_pair.lt_of_lt_of_le

  theorem lt_of_le_of_lt [trans] : a ≤ b → b < c → a < c := !order_pair.lt_of_le_of_lt

  private theorem lt_irrefl (s' : order_pair A) (a : A) : ¬ a < a := !order_pair.lt_irrefl

  private theorem lt_trans (s' : order_pair A) (a b c: A) (lt_ab : a < b) (lt_bc : b < c) : a < c :=
    lt_of_lt_of_le lt_ab (le_of_lt lt_bc)

  definition order_pair.to_strict_order [trans-instance] [coercion] [reducible] : strict_order A :=
  ⦃ strict_order, s, lt_irrefl := lt_irrefl s, lt_trans := lt_trans s ⦄

  theorem gt_of_gt_of_ge [trans] (H1 : a > b) (H2 : b ≥ c) : a > c := lt_of_le_of_lt H2 H1

  theorem gt_of_ge_of_gt [trans] (H1 : a ≥ b) (H2 : b > c) : a > c := lt_of_lt_of_le H2 H1

  theorem not_le_of_gt (H : a > b) : ¬ a ≤ b :=
  assume H1 : a ≤ b,
  lt.irrefl _ (lt_of_lt_of_le H H1)

  theorem not_lt_of_ge (H : a ≥ b) : ¬ a < b :=
  assume H1 : a < b,
  lt.irrefl _ (lt_of_le_of_lt H H1)
end

structure strong_order_pair [class] (A : Type) extends weak_order A, has_lt A :=
(le_iff_lt_or_eq : ∀a b, le a b ↔ lt a b ∨ a = b)
(lt_irrefl : ∀ a, ¬ lt a a)

theorem le_iff_lt_or_eq [s : strong_order_pair A] {a b : A} : a ≤ b ↔ a < b ∨ a = b :=
!strong_order_pair.le_iff_lt_or_eq

theorem lt_or_eq_of_le [s : strong_order_pair A] {a b : A} (le_ab : a ≤ b) : a < b ∨ a = b :=
iff.mp le_iff_lt_or_eq le_ab

theorem le_of_lt_or_eq [s : strong_order_pair A] {a b : A} (lt_or_eq : a < b ∨ a = b) : a ≤ b :=
iff.mpr le_iff_lt_or_eq lt_or_eq

private theorem lt_irrefl' [s : strong_order_pair A] (a : A) : ¬ a < a :=
!strong_order_pair.lt_irrefl

private theorem le_of_lt' [s : strong_order_pair A] (a b : A) : a < b → a ≤ b :=
take Hlt, le_of_lt_or_eq (or.inl Hlt)

private theorem lt_iff_le_and_ne [s : strong_order_pair A] {a b : A} : a < b ↔ (a ≤ b ∧ a ≠ b) :=
iff.intro
  (take Hlt, and.intro (le_of_lt_or_eq (or.inl Hlt)) (take Hab, absurd (Hab ▸ Hlt) !lt_irrefl'))
  (take Hand,
   have Hor : a < b ∨ a = b, from lt_or_eq_of_le (and.left Hand),
   or_resolve_left Hor (and.right Hand))

theorem lt_of_le_of_ne [s : strong_order_pair A] {a b : A} : a ≤ b → a ≠ b → a < b :=
take H1 H2, iff.mpr lt_iff_le_and_ne (and.intro H1 H2)

private theorem ne_of_lt' [s : strong_order_pair A] {a b : A} (H : a < b) : a ≠ b :=
and.right ((iff.mp lt_iff_le_and_ne) H)

private theorem lt_of_lt_of_le' [s : strong_order_pair A] (a b c : A) : a < b → b ≤ c → a < c :=
assume lt_ab : a < b,
assume le_bc : b ≤ c,
have le_ac : a ≤ c, from le.trans (le_of_lt' _ _ lt_ab) le_bc,
have ne_ac : a ≠ c, from
  assume eq_ac : a = c,
  have le_ba : b ≤ a, from eq_ac⁻¹ ▸ le_bc,
  have eq_ab : a = b, from le.antisymm  (le_of_lt' _ _ lt_ab) le_ba,
  show false, from ne_of_lt' lt_ab eq_ab,
show a < c, from iff.mpr (lt_iff_le_and_ne) (and.intro le_ac ne_ac)

theorem lt_of_le_of_lt' [s : strong_order_pair A] (a b c : A) : a ≤ b → b < c → a < c :=
assume le_ab : a ≤ b,
assume lt_bc : b < c,
have le_ac : a ≤ c, from le.trans le_ab (le_of_lt' _ _ lt_bc),
have ne_ac : a ≠ c, from
  assume eq_ac : a = c,
  have le_cb : c ≤ b, from eq_ac ▸ le_ab,
  have eq_bc : b = c, from le.antisymm  (le_of_lt' _ _ lt_bc) le_cb,
  show false, from ne_of_lt' lt_bc eq_bc,
show a < c, from iff.mpr (lt_iff_le_and_ne) (and.intro le_ac ne_ac)

definition strong_order_pair.to_order_pair [trans-instance] [coercion] [reducible]
    [s : strong_order_pair A] : order_pair A :=
⦃ order_pair, s,
  lt_irrefl := lt_irrefl',
  le_of_lt := le_of_lt',
  lt_of_le_of_lt := lt_of_le_of_lt',
  lt_of_lt_of_le := lt_of_lt_of_le' ⦄

/- linear orders -/

structure linear_order_pair [class] (A : Type) extends order_pair A, linear_weak_order A

structure linear_strong_order_pair [class] (A : Type) extends strong_order_pair A,
    linear_weak_order A

definition linear_strong_order_pair.to_linear_order_pair [trans-instance] [coercion] [reducible]
    [s : linear_strong_order_pair A] : linear_order_pair A :=
⦃ linear_order_pair, s, strong_order_pair.to_order_pair ⦄

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

  theorem le_of_not_gt {a b : A} (H : ¬ a > b) : a ≤ b :=
  lt.by_cases (assume H', absurd H' H) (assume H', H' ▸ !le.refl) (assume H', le_of_lt H')

  theorem lt_of_not_ge {a b : A} (H : ¬ a ≥ b) : a < b :=
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

open decidable

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
      have H1 : b ≤ a, from le_of_not_gt H,
      by_cases
        (assume H2 : b < a, inr (not_le_of_gt H2))
        (assume H2 : ¬ b < a, inl (le_of_not_gt H2)))

  definition has_decidable_eq [instance] : decidable (a = b) :=
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

  private definition dlo_min (a b : A) : A := if a ≤ b then a else b

  private definition dlo_max (a b : A) : A := if a ≤ b then b else a

  private theorem dlo_min_le_left (a b : A) : dlo_min a b ≤ a :=
  by_cases
    (assume H : a ≤ b, by rewrite [↑dlo_min, if_pos H]; apply le.refl)
    (assume H : ¬ a ≤ b, by rewrite [↑dlo_min, if_neg H]; apply le_of_lt (lt_of_not_ge H))

  private theorem dlo_min_le_right (a b : A) : dlo_min a b ≤ b :=
  by_cases
    (assume H : a ≤ b, by rewrite [↑dlo_min, if_pos H]; apply H)
    (assume H : ¬ a ≤ b, by rewrite [↑dlo_min, if_neg H]; apply le.refl)

  private theorem le_dlo_min (a b c : A) (H₁ : c ≤ a) (H₂ : c ≤ b) : c ≤ dlo_min a b :=
  by_cases
    (assume H : a ≤ b, by rewrite [↑dlo_min, if_pos H]; apply H₁)
    (assume H : ¬ a ≤ b, by rewrite [↑dlo_min, if_neg H]; apply H₂)

  private theorem le_dlo_max_left (a b : A) : a ≤ dlo_max a b :=
  by_cases
    (assume H : a ≤ b, by rewrite [↑dlo_max, if_pos H]; apply H)
    (assume H : ¬ a ≤ b, by rewrite [↑dlo_max, if_neg H]; apply le.refl)

  private theorem le_dlo_max_right (a b : A) : b ≤ dlo_max a b :=
  by_cases
    (assume H : a ≤ b, by rewrite [↑dlo_max, if_pos H]; apply le.refl)
    (assume H : ¬ a ≤ b, by rewrite [↑dlo_max, if_neg H]; apply le_of_lt (lt_of_not_ge H))

  private theorem dlo_max_le (a b c : A) (H₁ : a ≤ c) (H₂ : b ≤ c) : dlo_max a b ≤ c :=
  by_cases
    (assume H : a ≤ b, by rewrite [↑dlo_max, if_pos H]; apply H₂)
    (assume H : ¬ a ≤ b, by rewrite [↑dlo_max, if_neg H]; apply H₁)

  definition decidable_linear_order.to_lattice [trans-instance] [coercion] [reducible] :
    lattice A :=
  ⦃ lattice, s,
    min := dlo_min,
    max := dlo_max,
    min_le_left := dlo_min_le_left,
    min_le_right := dlo_min_le_right,
    le_min := le_dlo_min,
    le_max_left := le_dlo_max_left,
    le_max_right := le_dlo_max_right,
    max_le := dlo_max_le ⦄

  /- These don't require decidability, but it is not clear whether it is worth breaking out
     a new class, linearly_ordered_lattice. Currently nat is the only instance that doesn't
     use decidable_linear_order (because max and min are defined separately, in init),
     so we simply reprove these theorems there. -/

  theorem lt_min {a b c : A} (H₁ : a < b) (H₂ : a < c) : a < min b c :=
  by_cases
    (assume H : b ≤ c, by rewrite (min_eq_left H); apply H₁)
    (assume H : ¬ b ≤ c,
      assert H' : c ≤ b, from le_of_lt (lt_of_not_ge H),
      by rewrite (min_eq_right H'); apply H₂)

  theorem max_lt {a b c : A} (H₁ : a < c) (H₂ : b < c) : max a b < c :=
  by_cases
    (assume H : a ≤ b, by rewrite (max_eq_right H); apply H₂)
    (assume H : ¬ a ≤ b,
      assert H' : b ≤ a, from le_of_lt (lt_of_not_ge H),
      by rewrite (max_eq_left H'); apply H₁)
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
