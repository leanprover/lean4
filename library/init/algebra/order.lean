/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic
/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

set_option old_structure_cmd true

universe u
variables {α : Type u}

class weak_order (α : Type u) extends has_le α :=
(le_refl : ∀ a : α, a ≤ a)
(le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
(le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)

class linear_weak_order (α : Type u) extends weak_order α :=
(le_total : ∀ a b : α, a ≤ b ∨ b ≤ a)

class strict_order (α : Type u) extends has_lt α :=
(lt_irrefl : ∀ a : α, ¬ a < a)
(lt_trans : ∀ a b c : α, a < b → b < c → a < c)

/- structures with a weak and a strict order -/
class order_pair (α : Type u) extends weak_order α, has_lt α :=
(le_of_lt : ∀ a b : α, a < b → a ≤ b)
(lt_of_lt_of_le : ∀ a b c : α, a < b → b ≤ c → a < c)
(lt_of_le_of_lt : ∀ a b c : α, a ≤ b → b < c → a < c)
(lt_irrefl : ∀ a : α, ¬ a < a)

class strong_order_pair (α : Type u) extends weak_order α, has_lt α :=
(le_iff_lt_or_eq : ∀ a b : α, a ≤ b ↔ a < b ∨ a = b)
(lt_irrefl : ∀ a : α, ¬ a < a)

class linear_order_pair (α : Type u) extends order_pair α, linear_weak_order α

class linear_strong_order_pair (α : Type u) extends strong_order_pair α, linear_weak_order α

@[refl] lemma le_refl [weak_order α] : ∀ a : α, a ≤ a :=
weak_order.le_refl

@[trans] lemma le_trans [weak_order α] : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
weak_order.le_trans

lemma le_antisymm [weak_order α] : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
weak_order.le_antisymm

lemma le_of_eq [weak_order α] {a b : α} : a = b → a ≤ b :=
λ h, h ▸ le_refl a

@[trans] lemma ge_trans [weak_order α] : ∀ {a b c : α}, a ≥ b → b ≥ c → a ≥ c :=
λ a b c h₁ h₂, le_trans h₂ h₁

lemma le_total [linear_weak_order α] : ∀ a b : α, a ≤ b ∨ b ≤ a :=
linear_weak_order.le_total

lemma le_of_not_ge [linear_weak_order α] {a b : α} : ¬ a ≥ b → a ≤ b :=
or.resolve_left (le_total b a)

lemma le_of_not_le [linear_weak_order α] {a b : α} : ¬ a ≤ b → b ≤ a :=
or.resolve_left (le_total a b)

lemma lt_irrefl [strict_order α] : ∀ a : α, ¬ a < a :=
strict_order.lt_irrefl

lemma gt_irrefl [strict_order α] : ∀ a : α, ¬ a > a :=
lt_irrefl

@[trans] lemma lt_trans [strict_order α] : ∀ {a b c : α}, a < b → b < c → a < c :=
strict_order.lt_trans

def lt.trans := @lt_trans

@[trans] lemma gt_trans [strict_order α] : ∀ {a b c : α}, a > b → b > c → a > c :=
λ a b c h₁ h₂, lt_trans h₂ h₁

def gt.trans := @gt_trans

lemma ne_of_lt [strict_order α] {a b : α} (h : a < b) : a ≠ b :=
λ he, absurd h (he ▸ lt_irrefl a)

lemma ne_of_gt [strict_order α] {a b : α} (h : a > b) : a ≠ b :=
λ he, absurd h (he ▸ lt_irrefl a)

lemma lt_asymm [strict_order α] {a b : α} (h : a < b) : ¬ b < a :=
λ h1 : b < a, lt_irrefl a (lt_trans h h1)

lemma not_lt_of_gt [strict_order α] {a b : α} (h : a > b) : ¬ a < b :=
lt_asymm h

lemma le_of_lt [order_pair α] : ∀ {a b : α}, a < b → a ≤ b :=
order_pair.le_of_lt

@[trans] lemma lt_of_lt_of_le [order_pair α] : ∀ {a b c : α}, a < b → b ≤ c → a < c :=
order_pair.lt_of_lt_of_le

@[trans] lemma lt_of_le_of_lt [order_pair α] : ∀ {a b c : α}, a ≤ b → b < c → a < c :=
order_pair.lt_of_le_of_lt

@[trans] lemma gt_of_gt_of_ge [order_pair α] {a b c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
lt_of_le_of_lt h₂ h₁

@[trans] lemma gt_of_ge_of_gt [order_pair α] {a b c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
lt_of_lt_of_le h₂ h₁

instance order_pair.to_strict_order [s : order_pair α] : strict_order α :=
{ s with
  lt_irrefl := order_pair.lt_irrefl,
  lt_trans  := λ a b c h₁ h₂, lt_of_lt_of_le h₁ (le_of_lt h₂) }

lemma not_le_of_gt [order_pair α] {a b : α} (h : a > b) : ¬ a ≤ b :=
λ h₁, lt_irrefl b (lt_of_lt_of_le h h₁)

lemma not_lt_of_ge [order_pair α] {a b : α} (h : a ≥ b) : ¬ a < b :=
λ h₁, lt_irrefl b (lt_of_le_of_lt h h₁)

lemma le_iff_lt_or_eq [strong_order_pair α] : ∀ {a b : α}, a ≤ b ↔ a < b ∨ a = b :=
strong_order_pair.le_iff_lt_or_eq

lemma lt_or_eq_of_le [strong_order_pair α] : ∀ {a b : α}, a ≤ b → a < b ∨ a = b :=
λ a b h, iff.mp le_iff_lt_or_eq h

lemma le_of_lt_or_eq [strong_order_pair α] : ∀ {a b : α}, (a < b ∨ a = b) → a ≤ b :=
λ a b h, iff.mpr le_iff_lt_or_eq h

lemma lt_of_le_of_ne [strong_order_pair α] {a b : α} : a ≤ b → a ≠ b → a < b :=
λ h₁ h₂, or.resolve_right (lt_or_eq_of_le h₁) h₂

private lemma lt_irrefl' [strong_order_pair α] : ∀ a : α, ¬ a < a :=
strong_order_pair.lt_irrefl

private lemma le_of_lt' [strong_order_pair α] ⦃a b : α⦄ (h : a < b) : a ≤ b :=
le_of_lt_or_eq (or.inl h)

private lemma lt_of_lt_of_le' [strong_order_pair α] (a b c : α) (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
have a ≤ c, from le_trans (le_of_lt' h₁) h₂,
or.elim (lt_or_eq_of_le this)
  (λ h : a < c, h)
  (λ h : a = c,
    have b ≤ a, from h.symm ▸ h₂,
    have a = b, from le_antisymm (le_of_lt' h₁) this,
    absurd h₁ (this ▸ lt_irrefl' a))

private lemma lt_of_le_of_lt' [strong_order_pair α] (a b c : α) (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
have a ≤ c, from le_trans h₁ (le_of_lt' h₂),
or.elim (lt_or_eq_of_le this)
  (λ h : a < c, h)
  (λ h : a = c,
    have c ≤ b, from h ▸ h₁,
    have c = b, from le_antisymm this (le_of_lt' h₂),
    absurd h₂ (this ▸ lt_irrefl' c))

instance strong_order_pair.to_order_pair [s : strong_order_pair α] : order_pair α :=
{ s with
  lt_irrefl      := lt_irrefl',
  le_of_lt       := le_of_lt',
  lt_of_le_of_lt := lt_of_le_of_lt',
  lt_of_lt_of_le := lt_of_lt_of_le'}

instance linear_strong_order_pair.to_linear_order_pair [s : linear_strong_order_pair α] : linear_order_pair α :=
{ s with
  lt_irrefl      := lt_irrefl',
  le_of_lt       := le_of_lt',
  lt_of_le_of_lt := lt_of_le_of_lt',
  lt_of_lt_of_le := lt_of_lt_of_le'}

lemma lt_trichotomy [linear_strong_order_pair α] (a b : α) : a < b ∨ a = b ∨ b < a :=
or.elim (le_total a b)
  (λ h : a ≤ b, or.elim (lt_or_eq_of_le h)
    (λ h : a < b, or.inl h)
    (λ h : a = b, or.inr (or.inl h)))
  (λ h : b ≤ a, or.elim (lt_or_eq_of_le h)
    (λ h : b < a, or.inr (or.inr h))
    (λ h : b = a, or.inr (or.inl h.symm)))

lemma le_of_not_gt [linear_strong_order_pair α] {a b : α} (h : ¬ a > b) : a ≤ b :=
match lt_trichotomy a b with
| or.inl hlt          := le_of_lt hlt
| or.inr (or.inl heq) := heq ▸ le_refl a
| or.inr (or.inr hgt) := absurd hgt h
end

lemma lt_of_not_ge [linear_strong_order_pair α] {a b : α} (h : ¬ a ≥ b) : a < b :=
match lt_trichotomy a b with
| or.inl hlt          := hlt
| or.inr (or.inl heq) := absurd (heq ▸ le_refl a : a ≥ b) h
| or.inr (or.inr hgt) := absurd (le_of_lt hgt) h
end

lemma lt_or_ge [linear_strong_order_pair α] (a b : α) : a < b ∨ a ≥ b :=
match lt_trichotomy a b with
| or.inl hlt          := or.inl hlt
| or.inr (or.inl heq) := or.inr (heq ▸ le_refl a)
| or.inr (or.inr hgt) := or.inr (le_of_lt hgt)
end

lemma le_or_gt [linear_strong_order_pair α] (a b : α) : a ≤ b ∨ a > b :=
or.swap (lt_or_ge b a)

lemma lt_or_gt_of_ne [linear_strong_order_pair α] {a b : α} (h : a ≠ b) : a < b ∨ a > b :=
match lt_trichotomy a b with
| or.inl hlt          := or.inl hlt
| or.inr (or.inl heq) := absurd heq h
| or.inr (or.inr hgt) := or.inr hgt
end

lemma lt_iff_not_ge [linear_strong_order_pair α] (x y : α) : x < y ↔ ¬ x ≥ y :=
⟨not_le_of_gt, lt_of_not_ge⟩

/- The following lemma can be used when defining a decidable_linear_order instance, and the concrete structure
   does not have its own definition for decidable le  -/
def decidable_le_of_decidable_lt [linear_strong_order_pair α] [∀ a b : α, decidable (a < b)] (a b : α) : decidable (a ≤ b) :=
if h₁ : a < b      then is_true (le_of_lt h₁)
else if h₂ : b < a then is_false (not_le_of_gt h₂)
else                    is_true (le_of_not_gt h₂)

/- The following lemma can be used when defining a decidable_linear_order instance, and the concrete structure
   does not have its own definition for decidable le -/
def decidable_eq_of_decidable_lt [linear_strong_order_pair α] [∀ a b : α, decidable (a < b)] (a b : α) : decidable (a = b) :=
match decidable_le_of_decidable_lt a b with
| is_true h₁  :=
  match decidable_le_of_decidable_lt b a with
  | is_true h₂  := is_true (le_antisymm h₁ h₂)
  | is_false h₂ := is_false (λ he : a = b, h₂ (he ▸ le_refl a))
  end
| is_false h₁ := is_false (λ he : a = b, h₁ (he ▸ le_refl a))
end

class decidable_linear_order (α : Type u) extends linear_strong_order_pair α :=
(decidable_lt : decidable_rel lt)
(decidable_le : decidable_rel le) -- TODO(Leo): add default value using decidable_le_of_decidable_lt
(decidable_eq : decidable_eq α)   -- TODO(Leo): add default value using decidable_eq_of_decidable_lt

instance [decidable_linear_order α] (a b : α) : decidable (a < b) :=
decidable_linear_order.decidable_lt α a b

instance [decidable_linear_order α] (a b : α) : decidable (a ≤ b) :=
decidable_linear_order.decidable_le α a b

instance [decidable_linear_order α] (a b : α) : decidable (a = b) :=
decidable_linear_order.decidable_eq α a b

lemma eq_or_lt_of_not_lt [decidable_linear_order α] {a b : α} (h : ¬ a < b) : a = b ∨ b < a :=
if h₁ : a = b then or.inl h₁
else or.inr (lt_of_not_ge (λ hge, h (lt_of_le_of_ne hge h₁)))
