/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.classical init.meta.name init.algebra.classes
/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

set_option old_structure_cmd true

universe u
variables {α : Type u}

set_option auto_param.check_exists false
class preorder (α : Type u) extends has_le α, has_lt α :=
(le_refl : ∀ a : α, a ≤ a)
(le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
(lt := λ a b, a ≤ b ∧ ¬ b ≤ a)
(lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) . order_laws_tac)

class partial_order (α : Type u) extends preorder α :=
(le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)

class linear_order (α : Type u) extends partial_order α :=
(le_total : ∀ a b : α, a ≤ b ∨ b ≤ a)

@[refl] lemma le_refl [preorder α] : ∀ a : α, a ≤ a :=
preorder.le_refl

@[trans] lemma le_trans [preorder α] : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
preorder.le_trans

lemma lt_iff_le_not_le [preorder α] : ∀ {a b : α}, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) :=
preorder.lt_iff_le_not_le _

lemma lt_of_le_not_le [preorder α] : ∀ {a b : α}, a ≤ b → ¬ b ≤ a → a < b
| a b hab hba := lt_iff_le_not_le.mpr ⟨hab, hba⟩

lemma le_not_le_of_lt [preorder α] : ∀ {a b : α}, a < b → a ≤ b ∧ ¬ b ≤ a
| a b hab := lt_iff_le_not_le.mp hab

lemma le_antisymm [partial_order α] : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
partial_order.le_antisymm

lemma le_of_eq [preorder α] {a b : α} : a = b → a ≤ b :=
λ h, h ▸ le_refl a

lemma le_antisymm_iff [partial_order α] {a b : α} : a = b ↔ a ≤ b ∧ b ≤ a :=
⟨λe, ⟨le_of_eq e, le_of_eq e.symm⟩, λ⟨h1, h2⟩, le_antisymm h1 h2⟩

@[trans] lemma ge_trans [preorder α] : ∀ {a b c : α}, a ≥ b → b ≥ c → a ≥ c :=
λ a b c h₁ h₂, le_trans h₂ h₁

lemma le_total [linear_order α] : ∀ a b : α, a ≤ b ∨ b ≤ a :=
linear_order.le_total

lemma le_of_not_ge [linear_order α] {a b : α} : ¬ a ≥ b → a ≤ b :=
or.resolve_left (le_total b a)

lemma le_of_not_le [linear_order α] {a b : α} : ¬ a ≤ b → b ≤ a :=
or.resolve_left (le_total a b)

lemma lt_irrefl [preorder α] : ∀ a : α, ¬ a < a
| a haa := match le_not_le_of_lt haa with
  | ⟨h1, h2⟩ := false.rec _ (h2 h1)
  end

lemma gt_irrefl [preorder α] : ∀ a : α, ¬ a > a :=
lt_irrefl

@[trans] lemma lt_trans [preorder α] : ∀ {a b c : α}, a < b → b < c → a < c
| a b c hab hbc :=
  match le_not_le_of_lt hab, le_not_le_of_lt hbc with
  | ⟨hab, hba⟩, ⟨hbc, hcb⟩ := lt_of_le_not_le (le_trans hab hbc) (λ hca, hcb (le_trans hca hab))
  end

def lt.trans := @lt_trans

@[trans] lemma gt_trans [preorder α] : ∀ {a b c : α}, a > b → b > c → a > c :=
λ a b c h₁ h₂, lt_trans h₂ h₁

def gt.trans := @gt_trans

lemma ne_of_lt [preorder α] {a b : α} (h : a < b) : a ≠ b :=
λ he, absurd h (he ▸ lt_irrefl a)

lemma ne_of_gt [preorder α] {a b : α} (h : a > b) : a ≠ b :=
λ he, absurd h (he ▸ lt_irrefl a)

lemma lt_asymm [preorder α] {a b : α} (h : a < b) : ¬ b < a :=
λ h1 : b < a, lt_irrefl a (lt_trans h h1)

lemma not_lt_of_gt [linear_order α] {a b : α} (h : a > b) : ¬ a < b :=
lt_asymm h

lemma le_of_lt [preorder α] : ∀ {a b : α}, a < b → a ≤ b
| a b hab := (le_not_le_of_lt hab).left

@[trans] lemma lt_of_lt_of_le [preorder α] : ∀ {a b c : α}, a < b → b ≤ c → a < c
| a b c hab hbc :=
  let ⟨hab, hba⟩ := le_not_le_of_lt hab in
  lt_of_le_not_le (le_trans hab hbc) $ λ hca, hba (le_trans hbc hca)

@[trans] lemma lt_of_le_of_lt [preorder α] : ∀ {a b c : α}, a ≤ b → b < c → a < c
| a b c hab hbc :=
  let ⟨hbc, hcb⟩ := le_not_le_of_lt hbc in
  lt_of_le_not_le (le_trans hab hbc) $ λ hca, hcb (le_trans hca hab)

@[trans] lemma gt_of_gt_of_ge [preorder α] {a b c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
lt_of_le_of_lt h₂ h₁

@[trans] lemma gt_of_ge_of_gt [preorder α] {a b c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
lt_of_lt_of_le h₂ h₁

lemma not_le_of_gt [preorder α] {a b : α} (h : a > b) : ¬ a ≤ b :=
(le_not_le_of_lt h).right

lemma not_lt_of_ge [preorder α] {a b : α} (h : a ≥ b) : ¬ a < b :=
λ hab, not_le_of_gt hab h

lemma lt_or_eq_of_le [partial_order α] : ∀ {a b : α}, a ≤ b → a < b ∨ a = b
| a b hab := classical.by_cases
  (λ hba : b ≤ a, or.inr (le_antisymm hab hba))
  (λ hba, or.inl (lt_of_le_not_le hab hba))

lemma le_of_lt_or_eq [preorder α] : ∀ {a b : α}, (a < b ∨ a = b) → a ≤ b
| a b (or.inl hab) := le_of_lt hab
| a b (or.inr hab) := hab ▸ le_refl _

lemma le_iff_lt_or_eq [partial_order α] : ∀ {a b : α}, a ≤ b ↔ a < b ∨ a = b
| a b := ⟨lt_or_eq_of_le, le_of_lt_or_eq⟩

lemma lt_of_le_of_ne [partial_order α] {a b : α} : a ≤ b → a ≠ b → a < b :=
λ h₁ h₂, or.resolve_right (lt_or_eq_of_le h₁) h₂

lemma lt_trichotomy [linear_order α] (a b : α) : a < b ∨ a = b ∨ b < a :=
or.elim (le_total a b)
  (λ h : a ≤ b, or.elim (lt_or_eq_of_le h)
    (λ h : a < b, or.inl h)
    (λ h : a = b, or.inr (or.inl h)))
  (λ h : b ≤ a, or.elim (lt_or_eq_of_le h)
    (λ h : b < a, or.inr (or.inr h))
    (λ h : b = a, or.inr (or.inl h.symm)))

lemma le_of_not_gt [linear_order α] {a b : α} (h : ¬ a > b) : a ≤ b :=
match lt_trichotomy a b with
| or.inl hlt          := le_of_lt hlt
| or.inr (or.inl heq) := heq ▸ le_refl a
| or.inr (or.inr hgt) := absurd hgt h
end

lemma lt_of_not_ge [linear_order α] {a b : α} (h : ¬ a ≥ b) : a < b :=
match lt_trichotomy a b with
| or.inl hlt          := hlt
| or.inr (or.inl heq) := absurd (heq ▸ le_refl a : a ≥ b) h
| or.inr (or.inr hgt) := absurd (le_of_lt hgt) h
end

lemma lt_or_ge [linear_order α] (a b : α) : a < b ∨ a ≥ b :=
match lt_trichotomy a b with
| or.inl hlt          := or.inl hlt
| or.inr (or.inl heq) := or.inr (heq ▸ le_refl a)
| or.inr (or.inr hgt) := or.inr (le_of_lt hgt)
end

lemma le_or_gt [linear_order α] (a b : α) : a ≤ b ∨ a > b :=
or.swap (lt_or_ge b a)

lemma lt_or_gt_of_ne [linear_order α] {a b : α} (h : a ≠ b) : a < b ∨ a > b :=
match lt_trichotomy a b with
| or.inl hlt          := or.inl hlt
| or.inr (or.inl heq) := absurd heq h
| or.inr (or.inr hgt) := or.inr hgt
end

lemma le_of_eq_or_lt [preorder α] {a b : α} (h : a = b ∨ a < b) : a ≤ b :=
or.elim h le_of_eq le_of_lt

lemma ne_iff_lt_or_gt [linear_order α] {a b : α} : a ≠ b ↔ a < b ∨ a > b :=
⟨lt_or_gt_of_ne, λo, or.elim o ne_of_lt ne_of_gt⟩

lemma lt_iff_not_ge [linear_order α] (x y : α) : x < y ↔ ¬ x ≥ y :=
⟨not_le_of_gt, lt_of_not_ge⟩

instance decidable_lt_of_decidable_le [preorder α]
  [decidable_rel ((≤) : α → α → Prop)] :
  decidable_rel ((<) : α → α → Prop)
| a b :=
  if hab : a ≤ b then
    if hba : b ≤ a then
      is_false $ λ hab', not_le_of_gt hab' hba
    else
      is_true $ lt_of_le_not_le hab hba
  else
    is_false $ λ hab', hab (le_of_lt hab')

instance decidable_eq_of_decidable_le [partial_order α]
  [decidable_rel ((≤) : α → α → Prop)] :
  decidable_eq α
| a b :=
  if hab : a ≤ b then
    if hba : b ≤ a then
      is_true (le_antisymm hab hba)
    else
      is_false (λ heq, hba (heq ▸ le_refl _))
  else
    is_false (λ heq, hab (heq ▸ le_refl _))

class decidable_linear_order (α : Type u) extends linear_order α :=
(decidable_le : decidable_rel (≤))
(decidable_eq : decidable_eq α := @decidable_eq_of_decidable_le _ _ decidable_le)
(decidable_lt : decidable_rel ((<) : α → α → Prop) :=
    @decidable_lt_of_decidable_le _ _ decidable_le)

instance [decidable_linear_order α] (a b : α) : decidable (a < b) :=
decidable_linear_order.decidable_lt α a b

instance [decidable_linear_order α] (a b : α) : decidable (a ≤ b) :=
decidable_linear_order.decidable_le α a b

instance [decidable_linear_order α] (a b : α) : decidable (a = b) :=
decidable_linear_order.decidable_eq α a b

lemma eq_or_lt_of_not_lt [decidable_linear_order α] {a b : α} (h : ¬ a < b) : a = b ∨ b < a :=
if h₁ : a = b then or.inl h₁
else or.inr (lt_of_not_ge (λ hge, h (lt_of_le_of_ne hge h₁)))

instance [decidable_linear_order α] : is_total_preorder α (≤) :=
{trans := @le_trans _ _, total := le_total}

/- TODO(Leo): decide whether we should keep this instance or not -/
instance is_strict_weak_order_of_decidable_linear_order [decidable_linear_order α] : is_strict_weak_order α (<) :=
is_strict_weak_order_of_is_total_preorder lt_iff_not_ge

/- TODO(Leo): decide whether we should keep this instance or not -/
instance is_strict_total_order_of_decidable_linear_order [decidable_linear_order α] : is_strict_total_order α (<) :=
{ trichotomous := lt_trichotomy }
