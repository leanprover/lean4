/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

namespace Lean.Tailrec

universe u

-- section utils

-- open Nat


-- theorem le_succ_iff {m n : Nat} : m ≤ n.succ ↔ m ≤ n ∨ m = n.succ := by
--   refine ⟨fun hmn ↦ (Nat.lt_or_eq_of_le hmn).imp_left le_of_lt_succ, ?_⟩
--   rintro (hmn | rfl)
--   · exact le_succ_of_le hmn
--   · exact Nat.le_refl _

-- @[elab_as_elim]
-- def leRec {n} {motive : (m : Nat) → n ≤ m → Sort _}
--     (refl : motive n (Nat.le_refl _))
--     (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h)) :
--     ∀ {m} (h : n ≤ m), motive m h
--   | 0, H => Nat.eq_zero_of_le_zero H ▸ refl
--   | m + 1, H =>
--     (le_succ_iff.1 H).by_cases
--       (fun h : n ≤ m ↦ le_succ_of_le h <| leRec refl le_succ_of_le h)
--       (fun h : n = m + 1 ↦ h ▸ refl)

-- end utils

section fixpoint

variable {α : Type u}

variable (rel : α → α → Prop)
variable (rel_refl : ∀ {x}, rel x x)
variable (rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z)
variable (rel_antisymm : ∀ {x y}, rel x y → rel y x → x = y)

def monotone (f : α → α) : Prop := ∀ x y, rel x y → rel (f x) (f y)

def chain (c : α → Prop) : Prop := ∀ x y , c x → c y → rel x y ∨ rel y x

variable (csup : (α → Prop) → α)

variable (csup_spec : ∀ {c} (_ : chain rel c) {x : α},
  rel (csup c) x ↔ (∀ y, c y → rel y x))

include csup_spec in
theorem csup_le (hchain : chain rel c) : (∀ y, c y → rel y x) → rel (csup c) x :=
  (csup_spec hchain).mpr

include rel_refl csup_spec in
theorem le_csup (hchain : chain rel c) {y} (hy : c y) : rel y (csup c) :=
  (csup_spec hchain).mp rel_refl y hy

inductive iterates (f : α → α) : α → Prop where
  | step : iterates f x → iterates f (f x)
  | sup : chain rel c → (∀ x, c x → iterates f x) → iterates f (csup c)

def bot := csup (fun _ => False)

include csup_spec in
theorem bot_le : rel (bot csup) x := by
  apply csup_le rel csup csup_spec
  · intro x y hx hy; contradiction
  · intro x hx; contradiction

include rel_refl rel_trans csup_spec in
theorem chain_iterates {f : α → α} (hf : monotone rel f) : chain rel (iterates rel csup f) := by
  intros x y hx hy
  induction hx generalizing y
  case step x hx ih =>
    induction hy
    case step y hy _ =>
      cases ih y hy
      · left; apply hf; assumption
      · right; apply hf; assumption
    case sup c hchain hi ih2 =>
      show rel (f x) (csup c) ∨ rel (csup c) (f x)
      by_cases h : ∃ z, c z ∧ rel (f x) z
      · left
        obtain ⟨z, hz, hfz⟩ := h
        apply rel_trans hfz
        apply le_csup rel rel_refl csup csup_spec hchain hz
      · right
        apply csup_le rel csup csup_spec hchain _
        intro z hz
        rw [not_exists] at h
        specialize h z
        rw [not_and] at h
        specialize h hz
        cases ih2 z hz
        next => contradiction
        next => assumption
  case sup c hchain hi ih =>
    show rel (csup c) y ∨ rel y (csup c)
    by_cases h : ∃ z, c z ∧ rel y z
    · right
      obtain ⟨z, hz, hfz⟩ := h
      apply rel_trans hfz
      apply le_csup rel rel_refl csup csup_spec hchain hz
    · left
      apply csup_le rel csup csup_spec hchain _
      intro z hz
      rw [not_exists] at h
      specialize h z
      rw [not_and] at h
      specialize h hz
      cases ih z hz y hy
      next => assumption
      next => contradiction

include rel_refl rel_trans csup_spec in
theorem csup_iterate_rel {f : α → α} (hf : monotone rel f) :
    rel (csup (iterates rel csup f)) (f (csup (iterates rel csup f))) := by
  apply csup_le rel csup csup_spec (chain_iterates rel rel_refl rel_trans csup csup_spec hf)
  intro x hx
  induction hx
  case step ih =>
    apply hf
    apply le_csup rel rel_refl csup csup_spec (chain_iterates rel rel_refl rel_trans csup csup_spec hf)
    assumption
  case sup c hchain hi ih =>
    apply csup_le rel csup csup_spec hchain
    intro y hy
    apply ih _ hy

include rel_refl rel_antisymm rel_trans csup_spec in
theorem csup_iterate_eq {f : α → α} (hf : monotone rel f) :
    csup (iterates rel csup f) = f (csup (iterates rel csup f)) := by
  apply rel_antisymm
  · exact csup_iterate_rel rel rel_refl rel_trans csup csup_spec hf
  · apply le_csup rel rel_refl csup csup_spec (chain_iterates rel rel_refl rel_trans csup csup_spec hf)
    apply iterates.step
    apply iterates.sup (chain_iterates rel rel_refl rel_trans csup csup_spec hf)
    intro y hy
    exact hy

end fixpoint

section flat_order

variable {α : Type u}

variable (b : α)

inductive Flat_order (b : α) : (x y : α) → Prop where
  | bot : Flat_order b b x
  | refl : Flat_order b x x

namespace Flat_order

theorem trans {x y z : α} (hxy : Flat_order b x y) (hyz : Flat_order b y z) : Flat_order b x z := by
  cases hxy <;> cases hyz <;> constructor

theorem antisymm {x y : α} (hxy : Flat_order b x y) (hyz : Flat_order b y x) : x = y := by
  cases hxy <;> cases hyz <;> constructor


noncomputable def csup (c : α → Prop) : α :=
  open Classical in
  if h : ∃ x, c x ∧ x ≠ b then
    Classical.choose h
  else
    b

open Classical in
private theorem Classical.some_spec₂ {α : Sort _} {p : α → Prop} {h : ∃ a, p a} (q : α → Prop)
    (hpq : ∀ a, p a → q a) : q (choose h) := hpq _ <| choose_spec _

theorem csup_spec {c} (hc : chain (Flat_order b) c) {x : α} :
    Flat_order b (csup b c) x ↔ (∀ y, c y → Flat_order b y x) := by
  unfold csup
  split
  next hex =>
    apply Classical.some_spec₂ (q := (Flat_order b · x ↔ (∀ y, c y → Flat_order b y x)))
    clear hex
    intro z ⟨hz, hnb⟩
    constructor
    · intro h y hy
      apply trans b _ h; clear h
      cases hc y z hy hz
      next => assumption
      next h =>
        cases h
        · contradiction
        · constructor
    · intro h
      cases h z hz
      · contradiction
      · constructor
  next hnotex =>
    constructor
    · intro h y hy; clear h
      suffices y = b by rw [this]; exact Flat_order.bot
      rw [not_exists] at hnotex
      specialize hnotex y
      rw [not_and] at hnotex
      specialize hnotex hy
      rw [@Classical.not_not] at hnotex
      assumption
    · intro; exact Flat_order.bot

end Flat_order




end flat_order

end Lean.Tailrec
