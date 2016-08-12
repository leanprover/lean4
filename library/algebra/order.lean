/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Weak orders "≤", strict orders "<", and structures that include both.
-/
import logic.eq logic.connectives algebra.binary algebra.priority
open eq function

variables {A : Type}

/- weak orders -/

structure weak_order [class] (A : Type) extends has_le A :=
(le_refl : ∀a, le a a)
(le_trans : ∀a b c, le a b → le b c → le a c)
(le_antisymm : ∀a b, le a b → le b a → a = b)

section
  variables [weak_order A]

  attribute [refl]
  theorem le.refl (a : A) : a ≤ a := weak_order.le_refl a

  theorem le_of_eq {a b : A} (H : a = b) : a ≤ b := H ▸ le.refl a

  attribute [trans]
  theorem le.trans {a b c : A} : a ≤ b → b ≤ c → a ≤ c := weak_order.le_trans a b c

  attribute [trans]
  theorem ge.trans {a b c : A} (H1 : a ≥ b) (H2: b ≥ c) : a ≥ c := le.trans H2 H1

  theorem le.antisymm {a b : A} : a ≤ b → b ≤ a → a = b := weak_order.le_antisymm a b

  -- Alternate syntax. (Abbreviations do not migrate well.)
  theorem eq_of_le_of_ge {a b : A} : a ≤ b → b ≤ a → a = b := le.antisymm
end

structure linear_weak_order [class] (A : Type) extends weak_order A :=
(le_total : ∀a b, le a b ∨ le b a)

section
  variables [linear_weak_order A]

  theorem le.total (a b : A) : a ≤ b ∨ b ≤ a := linear_weak_order.le_total a b

  theorem le_of_not_ge {a b : A} (H : ¬ a ≥ b) : a ≤ b := or.resolve_left (le.total b a) H
end

/- strict orders -/

structure strict_order [class] (A : Type) extends has_lt A :=
(lt_irrefl : ∀a, ¬ lt a a)
(lt_trans : ∀a b c, lt a b → lt b c → lt a c)

section
  variable [strict_order A]

  theorem lt.irrefl (a : A) : ¬ a < a := strict_order.lt_irrefl a
  theorem not_lt_self (a : A) : ¬ a < a := lt.irrefl a   -- alternate syntax

  theorem lt_self_iff_false (a : A) : a < a ↔ false :=
  iff_false_intro (lt.irrefl a)

  attribute [trans]
  theorem lt.trans {a b c : A} : a < b → b < c → a < c := strict_order.lt_trans a b c

  attribute [trans]
  theorem gt.trans {a b c : A} (H1 : a > b) (H2: b > c) : a > c := lt.trans H2 H1

  theorem ne_of_lt {a b : A} (lt_ab : a < b) : a ≠ b :=
  assume eq_ab : a = b,
  show false, from lt.irrefl b (eq_ab ▸ lt_ab)

  theorem ne_of_gt {a b : A} (gt_ab : a > b) : a ≠ b :=
  ne.symm (ne_of_lt gt_ab)

  theorem lt.asymm {a b : A} (H : a < b) : ¬ b < a :=
  assume H1 : b < a, lt.irrefl _ (lt.trans H H1)

  theorem not_lt_of_gt {a b : A} (H : a > b) : ¬ a < b := lt.asymm H    -- alternate syntax
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

  theorem le_of_lt : a < b → a ≤ b := order_pair.le_of_lt a b

  attribute [trans]
  theorem lt_of_lt_of_le : a < b → b ≤ c → a < c := order_pair.lt_of_lt_of_le a b c

  attribute [trans]
  theorem lt_of_le_of_lt : a ≤ b → b < c → a < c := order_pair.lt_of_le_of_lt a b c

  private theorem lt_irrefl (s' : order_pair A) (a : A) : ¬ a < a := order_pair.lt_irrefl a

  private theorem lt_trans (s' : order_pair A) (a b c: A) (lt_ab : a < b) (lt_bc : b < c) : a < c :=
    lt_of_lt_of_le lt_ab (le_of_lt lt_bc)

  attribute [instance]
  definition order_pair.to_strict_order : strict_order A :=
  ⦃ strict_order, s, lt_irrefl := lt_irrefl s, lt_trans := lt_trans s ⦄

  attribute [trans]
  theorem gt_of_gt_of_ge (H1 : a > b) (H2 : b ≥ c) : a > c := lt_of_le_of_lt H2 H1

  attribute [trans]
  theorem gt_of_ge_of_gt (H1 : a ≥ b) (H2 : b > c) : a > c := lt_of_lt_of_le H2 H1

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

section strong_order_pair
  variable [strong_order_pair A]

  theorem le_iff_lt_or_eq {a b : A} : a ≤ b ↔ a < b ∨ a = b :=
  strong_order_pair.le_iff_lt_or_eq a b

  theorem lt_or_eq_of_le {a b : A} (le_ab : a ≤ b) : a < b ∨ a = b :=
  iff.mp le_iff_lt_or_eq le_ab

  theorem le_of_lt_or_eq {a b : A} (lt_or_eq : a < b ∨ a = b) : a ≤ b :=
  iff.mpr le_iff_lt_or_eq lt_or_eq

  private theorem lt_irrefl' (a : A) : ¬ a < a :=
  strong_order_pair.lt_irrefl a

  private theorem le_of_lt' (a b : A) : a < b → a ≤ b :=
  take Hlt, le_of_lt_or_eq (or.inl Hlt)

  private theorem lt_iff_le_and_ne {a b : A} : a < b ↔ (a ≤ b ∧ a ≠ b) :=
  iff.intro
    (take Hlt, and.intro (le_of_lt_or_eq (or.inl Hlt)) (take Hab, absurd (Hab ▸ Hlt) (lt_irrefl' b)))
    (take Hand,
     have Hor : a < b ∨ a = b, from lt_or_eq_of_le (and.left Hand),
     or_resolve_left Hor (and.right Hand))

  theorem lt_of_le_of_ne {a b : A} : a ≤ b → a ≠ b → a < b :=
  take H1 H2, iff.mpr lt_iff_le_and_ne (and.intro H1 H2)

  private theorem ne_of_lt' {a b : A} (H : a < b) : a ≠ b :=
  and.right ((iff.mp lt_iff_le_and_ne) H)

  private theorem lt_of_lt_of_le' (a b c : A) : a < b → b ≤ c → a < c :=
  assume lt_ab : a < b,
  assume le_bc : b ≤ c,
  have le_ac : a ≤ c, from le.trans (le_of_lt' _ _ lt_ab) le_bc,
  have ne_ac : a ≠ c, from
    assume eq_ac : a = c,
    have le_ba : b ≤ a, from symm eq_ac ▸ le_bc,
    have eq_ab : a = b, from le.antisymm  (le_of_lt' _ _ lt_ab) le_ba,
    show false, from ne_of_lt' lt_ab eq_ab,
  show a < c, from iff.mpr (lt_iff_le_and_ne) (and.intro le_ac ne_ac)

  theorem lt_of_le_of_lt' (a b c : A) : a ≤ b → b < c → a < c :=
  assume le_ab : a ≤ b,
  assume lt_bc : b < c,
  have le_ac : a ≤ c, from le.trans le_ab (le_of_lt' _ _ lt_bc),
  have ne_ac : a ≠ c, from
    assume eq_ac : a = c,
    have le_cb : c ≤ b, from eq_ac ▸ le_ab,
    have eq_bc : b = c, from le.antisymm  (le_of_lt' _ _ lt_bc) le_cb,
    show false, from ne_of_lt' lt_bc eq_bc,
  show a < c, from iff.mpr (lt_iff_le_and_ne) (and.intro le_ac ne_ac)
end strong_order_pair

attribute [instance]
definition strong_order_pair.to_order_pair
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

attribute [instance]
definition linear_strong_order_pair.to_linear_order_pair
    [s : linear_strong_order_pair A] : linear_order_pair A :=
⦃ linear_order_pair, s, strong_order_pair.to_order_pair ⦄

section
  variable [linear_strong_order_pair A]
  variables (a b c : A)

  theorem lt.trichotomy : a < b ∨ a = b ∨ b < a :=
  or.elim (le.total a b)
    (assume H : a ≤ b,
      or.elim (iff.mp le_iff_lt_or_eq H) (assume H1, or.inl H1) (assume H1, or.inr (or.inl H1)))
    (assume H : b ≤ a,
      or.elim (iff.mp le_iff_lt_or_eq H)
        (assume H1, or.inr (or.inr H1))
        (assume H1, or.inr (or.inl (symm H1))))

  theorem lt.by_cases {a b : A} {P : Prop}
    (H1 : a < b → P) (H2 : a = b → P) (H3 : b < a → P) : P :=
  or.elim (lt.trichotomy a b)
    (assume H, H1 H)
    (assume H, or.elim H (assume H', H2 H') (assume H', H3 H'))

  definition lt_ge_by_cases {a b : A} {P : Prop} (H1 : a < b → P) (H2 : a ≥ b → P) : P :=
  lt.by_cases H1 (λH, H2 (H ▸ le.refl a)) (λH, H2 (le_of_lt H))

  theorem le_of_not_gt {a b : A} (H : ¬ a > b) : a ≤ b :=
  lt.by_cases (assume H', absurd H' H) (assume H', H' ▸ (le.refl b)) (assume H', le_of_lt H')

  theorem lt_of_not_ge {a b : A} (H : ¬ a ≥ b) : a < b :=
  lt.by_cases
    (assume H', absurd (le_of_lt H') H)
    (assume H', absurd (H' ▸ le.refl b) H)
    (assume H', H')

  theorem lt_or_ge : a < b ∨ a ≥ b :=
  lt.by_cases
    (assume H1 : a < b, or.inl H1)
    (assume H1 : a = b, or.inr (H1 ▸ le.refl a))
    (assume H1 : a > b, or.inr (le_of_lt H1))

  theorem le_or_gt : a ≤ b ∨ a > b :=
  or.swap (lt_or_ge b a)

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

  attribute [instance]
  definition decidable_lt : decidable (a < b) :=
    @decidable_linear_order.decidable_lt _ _ _ _

  attribute [instance]
  definition decidable_le : decidable (a ≤ b) :=
  by_cases
    (assume H : a < b, tt (le_of_lt H))
    (assume H : ¬ a < b,
      have H1 : b ≤ a, from le_of_not_gt H,
      by_cases
        (assume H2 : b < a, ff (not_le_of_gt H2))
        (assume H2 : ¬ b < a, tt (le_of_not_gt H2)))

  attribute [instance]
  definition has_decidable_eq : decidable (a = b) :=
  by_cases
    (assume H : a ≤ b,
      by_cases
        (assume H1 : b ≤ a, tt (le.antisymm H H1))
        (assume H1 : ¬ b ≤ a, ff (assume H2 : a = b, H1 (H2 ▸ le.refl a))))
    (assume H : ¬ a ≤ b,
      (ff (assume H1 : a = b, H (H1 ▸ le.refl a))))

  theorem eq_or_lt_of_not_lt {a b : A} (H : ¬ a < b) : a = b ∨ b < a :=
    if Heq : a = b then or.inl Heq else or.inr (lt_of_not_ge (λ Hge, H (lt_of_le_of_ne Hge Heq)))

  theorem eq_or_lt_of_le {a b : A} (H : a ≤ b) : a = b ∨ a < b :=
  sorry
  /-
    begin
      cases eq_or_lt_of_not_lt (not_lt_of_ge H),
      exact or.inl a_1⁻¹,
      exact or.inr a_1
    end
  -/

  -- testing equality first may result in more definitional equalities
  definition lt.cases {B : Type} (a b : A) (t_lt t_eq t_gt : B) : B :=
  if a = b then t_eq else (if a < b then t_lt else t_gt)

  theorem lt.cases_of_eq {B : Type} {a b : A} {t_lt t_eq t_gt : B} (H : a = b) :
    lt.cases a b t_lt t_eq t_gt = t_eq := if_pos H

  theorem lt.cases_of_lt {B : Type} {a b : A} {t_lt t_eq t_gt : B} (H : a < b) :
    lt.cases a b t_lt t_eq t_gt = t_lt :=
  trans (if_neg (ne_of_lt H)) (if_pos H)

  theorem lt.cases_of_gt {B : Type} {a b : A} {t_lt t_eq t_gt : B} (H : a > b) :
    lt.cases a b t_lt t_eq t_gt = t_gt :=
  trans (if_neg (ne.symm (ne_of_lt H))) (if_neg (lt.asymm H))

  definition min (a b : A) : A := if a ≤ b then a else b
  definition max (a b : A) : A := if a ≤ b then b else a

  /- these show min and max form a lattice -/

  theorem min_le_left (a b : A) : min a b ≤ a :=
  sorry
  /-
  by_cases
    (assume H : a ≤ b, by rewrite [↑min, if_pos H])
    (assume H : ¬ a ≤ b, by rewrite [↑min, if_neg H]; apply le_of_lt (lt_of_not_ge H))
  -/

  theorem min_le_right (a b : A) : min a b ≤ b :=
  sorry
  /-
  by_cases
    (assume H : a ≤ b, by rewrite [↑min, if_pos H]; apply H)
    (assume H : ¬ a ≤ b, by rewrite [↑min, if_neg H])
  -/

  theorem le_min {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) : c ≤ min a b :=
  sorry
  /-
  by_cases
    (assume H : a ≤ b, by rewrite [↑min, if_pos H]; apply H₁)
    (assume H : ¬ a ≤ b, by rewrite [↑min, if_neg H]; apply H₂)
  -/

  theorem le_max_left (a b : A) : a ≤ max a b :=
  sorry
  /-
  by_cases
    (assume H : a ≤ b, by rewrite [↑max, if_pos H]; apply H)
    (assume H : ¬ a ≤ b, by rewrite [↑max, if_neg H])
  -/

  theorem le_max_right (a b : A) : b ≤ max a b :=
  sorry
  /-
  by_cases
    (assume H : a ≤ b, by rewrite [↑max, if_pos H])
    (assume H : ¬ a ≤ b, by rewrite [↑max, if_neg H]; apply le_of_lt (lt_of_not_ge H))
  -/

  theorem max_le {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) : max a b ≤ c :=
  sorry
  /-
  by_cases
    (assume H : a ≤ b, by rewrite [↑max, if_pos H]; apply H₂)
    (assume H : ¬ a ≤ b, by rewrite [↑max, if_neg H]; apply H₁)
  -/

  theorem le_max_left_iff_true (a b : A) : a ≤ max a b ↔ true :=
  iff_true_intro (le_max_left a b)

  theorem le_max_right_iff_true (a b : A) : b ≤ max a b ↔ true :=
  iff_true_intro (le_max_right a b)

  /- these are also proved for lattices, but with inf and sup in place of min and max -/

  theorem eq_min {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) (H₃ : ∀{d}, d ≤ a → d ≤ b → d ≤ c) :
    c = min a b :=
  le.antisymm (le_min H₁ H₂) (H₃ (min_le_left a b) (min_le_right a b))

  theorem min.comm (a b : A) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) (λ c H₁ H₂, le_min H₂ H₁)

  theorem min.assoc (a b c : A) : min (min a b) c = min a (min b c) :=
  sorry
  /-
  begin
    apply eq_min,
    { apply le.trans, apply min_le_left, apply min_le_left },
    { apply le_min, apply le.trans, apply min_le_left, apply min_le_right, apply min_le_right },
    { intros [d, H₁, H₂], apply le_min, apply le_min H₁, apply le.trans H₂, apply min_le_left,
      apply le.trans H₂, apply min_le_right }
  end
  -/

  theorem min.left_comm (a b c : A) : min a (min b c) = min b (min a c) :=
  binary.left_comm (@min.comm A s) (@min.assoc A s) a b c

  theorem min.right_comm (a b c : A) : min (min a b) c = min (min a c) b :=
  binary.right_comm (@min.comm A s) (@min.assoc A s) a b c

  theorem min_self (a : A) : min a a = a :=
  sorry -- by apply eq.symm; apply eq_min (le.refl a) !le.refl; intros; assumption

  theorem min_eq_left {a b : A} (H : a ≤ b) : min a b = a :=
  sorry -- by apply eq.symm; apply eq_min !le.refl H; intros; assumption

  theorem min_eq_right {a b : A} (H : b ≤ a) : min a b = b :=
  eq.subst (min.comm b a) (min_eq_left H)

  theorem eq_max {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) (H₃ : ∀{d}, a ≤ d → b ≤ d → c ≤ d) :
    c = max a b :=
  le.antisymm (H₃ (le_max_left a b) (le_max_right a b)) (max_le H₁ H₂)

  theorem max.comm (a b : A) : max a b = max b a :=
  eq_max (le_max_right a b) (le_max_left a b) (λ c H₁ H₂, max_le H₂ H₁)

  theorem max.assoc (a b c : A) : max (max a b) c = max a (max b c) :=
  sorry
  /-
  begin
    apply eq_max,
    { apply le.trans, apply le_max_left a b, apply le_max_left },
    { apply max_le, apply le.trans, apply le_max_right a b, apply le_max_left, apply le_max_right },
    { intros [d, H₁, H₂], apply max_le, apply max_le H₁, apply le.trans !le_max_left H₂,
      apply le.trans !le_max_right H₂}
  end
  -/

  theorem max.left_comm (a b c : A) : max a (max b c) = max b (max a c) :=
  binary.left_comm (@max.comm A s) (@max.assoc A s) a b c

  theorem max.right_comm (a b c : A) : max (max a b) c = max (max a c) b :=
  binary.right_comm (@max.comm A s) (@max.assoc A s) a b c

  theorem max_self (a : A) : max a a = a :=
  sorry -- by apply eq.symm; apply eq_max (le.refl a) !le.refl; intros; assumption

  theorem max_eq_left {a b : A} (H : b ≤ a) : max a b = a :=
  sorry -- by apply eq.symm; apply eq_max !le.refl H; intros; assumption

  theorem max_eq_right {a b : A} (H : a ≤ b) : max a b = b :=
  eq.subst (max.comm b a) (max_eq_left H)

  /- these rely on lt_of_lt -/

  theorem min_eq_left_of_lt {a b : A} (H : a < b) : min a b = a :=
  min_eq_left (le_of_lt H)

  theorem min_eq_right_of_lt {a b : A} (H : b < a) : min a b = b :=
  min_eq_right (le_of_lt H)

  theorem max_eq_left_of_lt {a b : A} (H : b < a) : max a b = a :=
  max_eq_left (le_of_lt H)

  theorem max_eq_right_of_lt {a b : A} (H : a < b) : max a b = b :=
  max_eq_right (le_of_lt H)

  /- these use the fact that it is a linear ordering -/

  theorem lt_min {a b c : A} (H₁ : a < b) (H₂ : a < c) : a < min b c :=
  sorry
  /-
  or.elim !le_or_gt
    (assume H : b ≤ c, by rewrite (min_eq_left H); apply H₁)
    (assume H : b > c, by rewrite (min_eq_right_of_lt H); apply H₂)
  -/

  theorem max_lt {a b c : A} (H₁ : a < c) (H₂ : b < c) : max a b < c :=
  sorry
  /-
  or.elim !le_or_gt
    (assume H : a ≤ b, by rewrite (max_eq_right H); apply H₂)
    (assume H : a > b, by rewrite (max_eq_left_of_lt H); apply H₁)
  -/
end

/- order instances -/

attribute [instance]
definition weak_order_Prop : weak_order Prop :=
⦃ weak_order,
  le           := λx y, x → y,
  le_refl      := λx, id,
  le_trans     := λa b c H1 H2 x, H2 (H1 x),
  le_antisymm  := λf g H1 H2, propext (and.intro H1 H2)
⦄

attribute [instance]
definition weak_order_fun (A B : Type) [weak_order B] : weak_order (A → B) :=
⦃ weak_order,
  le := λx y, ∀b, x b ≤ y b,
  le_refl := λf b, le.refl (f b),
  le_trans := λf g h H1 H2 b, le.trans (H1 b) (H2 b),
  le_antisymm := λf g H1 H2, funext (λb, le.antisymm (H1 b) (H2 b))
⦄

definition weak_order_dual {A : Type} (wo : weak_order A) : weak_order A :=
⦃ weak_order,
  le := λx y, y ≤ x,
  le_refl := le.refl,
  le_trans := sorry, -- take a b c `b ≤ a` `c ≤ b`, le.trans `c ≤ b` `b ≤ a`,
  le_antisymm := sorry ⦄ -- take a b `b ≤ a` `a ≤ b`, le.antisymm `a ≤ b` `b ≤ a` ⦄

lemma le_dual_eq_le {A : Type} (wo : weak_order A) (a b : A) :
  @le _ (@weak_order.to_has_le _ (weak_order_dual wo)) a b =
  @le _ (@weak_order.to_has_le _ wo) b a :=
rfl

-- what to do with the strict variants?
