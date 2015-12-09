/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.wf init.tactic init.num init.types init.path
open eq eq.ops decidable
open algebra sum
set_option class.force_new true

notation `ℕ` := nat

namespace nat
  protected definition rec_on [reducible] [recursor] [unfold 2]
                       {C : ℕ → Type} (n : ℕ) (H₁ : C 0) (H₂ : Π (a : ℕ), C a → C (succ a)) : C n :=
  nat.rec H₁ H₂ n

  protected definition cases_on [reducible] [recursor] [unfold 2]
                       {C : ℕ → Type} (n : ℕ) (H₁ : C 0) (H₂ : Π (a : ℕ), C (succ a)) : C n :=
  nat.rec H₁ (λ a ih, H₂ a) n

  protected definition no_confusion_type.{u} [reducible] (P : Type.{u}) (v₁ v₂ : ℕ) : Type.{u} :=
  nat.rec
    (nat.rec
       (P → lift P)
       (λ a₂ ih, lift P)
       v₂)
    (λ a₁ ih, nat.rec
       (lift P)
       (λ a₂ ih, (a₁ = a₂ → P) → lift P)
       v₂)
    v₁

  protected definition no_confusion [reducible] [unfold 4]
                       {P : Type} {v₁ v₂ : ℕ} (H : v₁ = v₂) : nat.no_confusion_type P v₁ v₂ :=
  eq.rec (λ H₁ : v₁ = v₁, nat.rec (λ h, lift.up h) (λ a ih h, lift.up (h (eq.refl a))) v₁) H H

  /- basic definitions on natural numbers -/
  inductive le (a : ℕ) : ℕ → Type :=
  | nat_refl : le a a    -- use nat_refl to avoid overloading le.refl
  | step : Π {b}, le a b → le a (succ b)

  definition nat_has_le [instance] [reducible] [priority nat.prio]: has_le nat := has_le.mk nat.le

  protected lemma le_refl [refl] : Π a : nat, a ≤ a :=
  le.nat_refl

  protected definition lt [reducible] (n m : ℕ) := succ n ≤ m
  definition nat_has_lt [instance] [reducible] [priority nat.prio] : has_lt nat := has_lt.mk nat.lt

  definition pred [unfold 1] (a : nat) : nat :=
  nat.cases_on a zero (λ a₁, a₁)

  -- add is defined in init.num

  protected definition sub (a b : nat) : nat :=
  nat.rec_on b a (λ b₁, pred)

  protected definition mul (a b : nat) : nat :=
  nat.rec_on b zero (λ b₁ r, r + a)

  definition nat_has_sub [instance] [reducible] [priority nat.prio] : has_sub nat :=
  has_sub.mk nat.sub

  definition nat_has_mul [instance] [reducible] [priority nat.prio] : has_mul nat :=
  has_mul.mk nat.mul

  /- properties of ℕ -/

  protected definition is_inhabited [instance] : inhabited nat :=
  inhabited.mk zero

  protected definition has_decidable_eq [instance] [priority nat.prio] : Π x y : nat, decidable (x = y)
  | has_decidable_eq zero     zero     := inl rfl
  | has_decidable_eq (succ x) zero     := inr (by contradiction)
  | has_decidable_eq zero     (succ y) := inr (by contradiction)
  | has_decidable_eq (succ x) (succ y) :=
      match has_decidable_eq x y with
      | inl xeqy := inl (by rewrite xeqy)
      | inr xney := inr (λ h : succ x = succ y, by injection h with xeqy; exact absurd xeqy xney)
      end

  /- properties of inequality -/

  protected theorem le_of_eq {n m : ℕ} (p : n = m) : n ≤ m := p ▸ !nat.le_refl

  theorem le_succ (n : ℕ) : n ≤ succ n := le.step !nat.le_refl

  theorem pred_le (n : ℕ) : pred n ≤ n := by cases n;repeat constructor

  theorem le_succ_iff_unit [simp] (n : ℕ) : n ≤ succ n ↔ unit :=
  iff_unit_intro (le_succ n)

  theorem pred_le_iff_unit [simp] (n : ℕ) : pred n ≤ n ↔ unit :=
  iff_unit_intro (pred_le n)

  protected theorem le_trans {n m k : ℕ} (H1 : n ≤ m) : m ≤ k → n ≤ k :=
  le.rec H1 (λp H2, le.step)

  theorem le_succ_of_le {n m : ℕ} (H : n ≤ m) : n ≤ succ m := nat.le_trans H !le_succ

  theorem le_of_succ_le {n m : ℕ} (H : succ n ≤ m) : n ≤ m := nat.le_trans !le_succ H

  protected theorem le_of_lt {n m : ℕ} (H : n < m) : n ≤ m := le_of_succ_le H

  theorem succ_le_succ {n m : ℕ} : n ≤ m → succ n ≤ succ m :=
  le.rec !nat.le_refl (λa b, le.step)

  theorem pred_le_pred {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
  le.rec !nat.le_refl (nat.rec (λa b, b) (λa b c, le.step))

  theorem le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
  pred_le_pred

  theorem le_succ_of_pred_le {n m : ℕ} : pred n ≤ m → n ≤ succ m :=
  nat.cases_on n le.step (λa, succ_le_succ)

  theorem not_succ_le_zero (n : ℕ) : ¬succ n ≤ 0 :=
  by intro H; cases H

  theorem succ_le_zero_iff_empty (n : ℕ) : succ n ≤ 0 ↔ empty :=
  iff_empty_intro !not_succ_le_zero

  theorem not_succ_le_self : Π {n : ℕ}, ¬succ n ≤ n :=
  nat.rec !not_succ_le_zero (λa b c, b (le_of_succ_le_succ c))

  theorem succ_le_self_iff_empty [simp] (n : ℕ) : succ n ≤ n ↔ empty :=
  iff_empty_intro not_succ_le_self

  theorem zero_le : Π (n : ℕ), 0 ≤ n :=
  nat.rec !nat.le_refl (λa, le.step)

  theorem zero_le_iff_unit [simp] (n : ℕ) : 0 ≤ n ↔ unit :=
  iff_unit_intro !zero_le

  theorem lt.step {n m : ℕ} : n < m → n < succ m := le.step

  theorem zero_lt_succ (n : ℕ) : 0 < succ n :=
  succ_le_succ !zero_le

  theorem zero_lt_succ_iff_unit [simp] (n : ℕ) : 0 < succ n ↔ unit :=
  iff_unit_intro (zero_lt_succ n)

  protected theorem lt_trans {n m k : ℕ} (H1 : n < m) : m < k → n < k :=
  nat.le_trans (le.step H1)

  protected theorem lt_of_le_of_lt {n m k : ℕ} (H1 : n ≤ m) : m < k → n < k :=
  nat.le_trans (succ_le_succ H1)

  protected theorem lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k := nat.le_trans

  protected theorem lt_irrefl (n : ℕ) : ¬n < n := not_succ_le_self

  theorem lt_self_iff_empty (n : ℕ) : n < n ↔ empty :=
  iff_empty_intro (λ H, absurd H (nat.lt_irrefl n))

  theorem self_lt_succ (n : ℕ) : n < succ n := !nat.le_refl

  theorem self_lt_succ_iff_unit [simp] (n : ℕ) : n < succ n ↔ unit :=
  iff_unit_intro (self_lt_succ n)

  theorem lt.base (n : ℕ) : n < succ n := !nat.le_refl

  theorem le_lt_antisymm {n m : ℕ} (H1 : n ≤ m) (H2 : m < n) : empty :=
  !nat.lt_irrefl (nat.lt_of_le_of_lt H1 H2)

  protected theorem le_antisymm {n m : ℕ} (H1 : n ≤ m) : m ≤ n → n = m :=
  le.cases_on H1 (λa, rfl) (λa b c, absurd (nat.lt_of_le_of_lt b c) !nat.lt_irrefl)

  theorem lt_le_antisymm {n m : ℕ} (H1 : n < m) (H2 : m ≤ n) : empty :=
  le_lt_antisymm H2 H1

  protected theorem nat.lt_asymm {n m : ℕ} (H1 : n < m) : ¬ m < n :=
  le_lt_antisymm (nat.le_of_lt H1)

  theorem not_lt_zero (a : ℕ) : ¬ a < 0 := !not_succ_le_zero

  theorem lt_zero_iff_empty [simp] (a : ℕ) : a < 0 ↔ empty :=
  iff_empty_intro (not_lt_zero a)

  protected theorem eq_sum_lt_of_le {a b : ℕ} (H : a ≤ b) : a = b ⊎ a < b :=
  le.cases_on H (inl rfl) (λn h, inr (succ_le_succ h))

  protected theorem le_of_eq_sum_lt {a b : ℕ} (H : a = b ⊎ a < b) : a ≤ b :=
  sum.rec_on H !nat.le_of_eq !nat.le_of_lt

  -- less-than is well-founded
  definition lt.wf [instance] : well_founded (lt : ℕ → ℕ → Type₀) :=
  begin
    constructor, intro n, induction n with n IH,
    { constructor, intros n H, exfalso, exact !not_lt_zero H},
    { constructor, intros m H,
      assert aux : ∀ {n₁} (hlt : m < n₁), succ n = n₁ → acc lt m,
        { intros n₁ hlt, induction hlt,
          { intro p, injection p with q, exact q ▸ IH},
          { intro p, injection p with q, exact (acc.inv (q ▸ IH) a)}},
      apply aux H rfl},
  end

  definition measure {A : Type} : (A → ℕ) → A → A → Type₀ :=
  inv_image lt

  definition measure.wf {A : Type} (f : A → ℕ) : well_founded (measure f) :=
  inv_image.wf f lt.wf

  theorem succ_lt_succ {a b : ℕ} : a < b → succ a < succ b :=
  succ_le_succ

  theorem lt_of_succ_lt {a b : ℕ} : succ a < b → a < b :=
  le_of_succ_le

  theorem lt_of_succ_lt_succ {a b : ℕ} : succ a < succ b → a < b :=
  le_of_succ_le_succ

  definition decidable_le [instance] [priority nat.prio] : Π a b : nat, decidable (a ≤ b)  :=
  nat.rec (λm, (decidable.inl !zero_le))
     (λn IH m, !nat.cases_on (decidable.inr (not_succ_le_zero n))
       (λm, decidable.rec (λH, inl (succ_le_succ H))
          (λH, inr (λa, H (le_of_succ_le_succ a))) (IH m)))

  definition decidable_lt [instance] [priority nat.prio] : Π a b : nat, decidable (a < b) :=
  λ a b, decidable_le (succ a) b

  protected theorem lt_sum_ge (a b : ℕ) : a < b ⊎ a ≥ b :=
  nat.rec (inr !zero_le) (λn, sum.rec
    (λh, inl (le_succ_of_le h))
    (λh, sum.rec_on (nat.eq_sum_lt_of_le h) (λe, inl (eq.subst e !nat.le_refl)) inr)) b

  protected definition lt_ge_by_cases {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a ≥ b → P) : P :=
  by_cases H1 (λh, H2 (sum.rec_on !nat.lt_sum_ge (λa, absurd a h) (λa, a)))

  protected definition lt_by_cases {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : b < a → P) : P :=
  nat.lt_ge_by_cases H1 (λh₁,
    nat.lt_ge_by_cases H3 (λh₂, H2 (nat.le_antisymm h₂ h₁)))

  protected theorem lt_trichotomy (a b : ℕ) : a < b ⊎ a = b ⊎ b < a :=
  nat.lt_by_cases (λH, inl H) (λH, inr (inl H)) (λH, inr (inr H))

  protected theorem eq_sum_lt_of_not_lt {a b : ℕ} (hnlt : ¬ a < b) : a = b ⊎ b < a :=
  sum.rec_on (nat.lt_trichotomy a b)
    (λ hlt, absurd hlt hnlt)
    (λ h, h)

  theorem lt_succ_of_le {a b : ℕ} : a ≤ b → a < succ b :=
  succ_le_succ

  theorem lt_of_succ_le {a b : ℕ} (h : succ a ≤ b) : a < b := h

  theorem succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b := h

  theorem succ_sub_succ_eq_sub [simp] (a b : ℕ) : succ a - succ b = a - b :=
  nat.rec (by esimp) (λ b, ap pred) b

  theorem sub_eq_succ_sub_succ (a b : ℕ) : a - b = succ a - succ b :=
  inverse !succ_sub_succ_eq_sub

  theorem zero_sub_eq_zero [simp] (a : ℕ) : 0 - a = 0 :=
  nat.rec rfl (λ a, ap pred) a

  theorem zero_eq_zero_sub (a : ℕ) : 0 = 0 - a :=
  inverse !zero_sub_eq_zero

  theorem sub_le (a b : ℕ) : a - b ≤ a :=
  nat.rec_on b !nat.le_refl (λ b₁, nat.le_trans !pred_le)

  theorem sub_le_iff_unit [simp] (a b : ℕ) : a - b ≤ a ↔ unit :=
  iff_unit_intro (sub_le a b)

  theorem sub_lt {a b : ℕ} (H1 : 0 < a) (H2 : 0 < b) : a - b < a :=
  !nat.cases_on (λh, absurd h !nat.lt_irrefl)
    (λa h, succ_le_succ (!nat.cases_on (λh, absurd h !nat.lt_irrefl)
      (λb c, tr_rev _ !succ_sub_succ_eq_sub !sub_le) H2)) H1

  theorem sub_lt_succ (a b : ℕ) : a - b < succ a :=
  lt_succ_of_le !sub_le

  theorem sub_lt_succ_iff_unit [simp] (a b : ℕ) : a - b < succ a ↔ unit :=
  iff_unit_intro !sub_lt_succ
end nat
