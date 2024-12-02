/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude

import Init.ByCases
import Init.RCases

namespace Lean.Tailrec


universe u v

class Order (α : Type u) where
  /-- The less-defined than relation -/
  rel : α → α → Prop
  rel_refl : ∀ {x}, rel x x
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_antisymm : ∀ {x y}, rel x y → rel y x → x = y


@[inherit_doc] infix:50 " ⊑ "  => Order.rel

section Order

variable {α  : Type u} [Order α]

theorem Order.rel_of_eq {x y : α} (h : x = y) : x ⊑ y := by cases h; apply rel_refl

def chain (c : α → Prop) : Prop := ∀ x y , c x → c y → x ⊑ y ∨ y ⊑ x

end Order

class CCPO (α : Type u) [Order α] where
  csup : (α → Prop) → α
  csup_spec {c : α → Prop} (hc : chain c) : csup c ⊑ x ↔ (∀ y, c y → y ⊑ x)

section CCPO

section monotone

variable {α : Type u} [Order α]
variable {β : Type v} [Order β]

def monotone (f : α → β) : Prop := ∀ x y, x ⊑ y → f x ⊑ f y

theorem monotone_const (c : β) : monotone (fun (_ : α) => c) :=
  fun _ _ _ => Order.rel_refl

theorem monotone_id : monotone (fun (x : α) => x) :=
  fun _ _ hxy => hxy

theorem monotone_letFun.{w} {γ : Sort w}
  (v : γ)
  (k : α → γ → β)
  (hmono : ∀ (y : γ), monotone (fun x => k x y)) :
  monotone fun (x : α) => letFun v (k x) := hmono v

theorem monotone_ite
  (c : Prop) [Decidable c]
  (k₁ : α → β)
  (k₂ : α → β)
  (hmono₁ : monotone (fun x => k₁ x))
  (hmono₂ : monotone (fun x => k₂ x)) :
  monotone fun x => if c then k₁ x else k₂ x := by
    split
    · apply hmono₁
    · apply hmono₂

theorem monotone_dite
  (c : Prop) [Decidable c]
  (k₁ : α → c → β)
  (k₂ : α → ¬ c → β)
  (hmono₁ : (h : c) → monotone (fun f => k₁ f h))
  (hmono₂ : (h : ¬ c) → monotone (fun f => k₂ f h)) :
  monotone fun x => dite c (k₁ x) (k₂ x) := by
    split
    · apply hmono₁
    · apply hmono₂

end monotone

open Order CCPO

variable {α  : Type u} [Order α] [CCPO α]

variable {c : α → Prop} (hchain : chain c)

include hchain in
theorem csup_le : (∀ y, c y → y ⊑ x) → csup c ⊑ x :=
  (csup_spec hchain).mpr

include hchain in
theorem le_csup {y} (hy : c y) : y ⊑ csup c :=
  (csup_spec hchain).mp rel_refl y hy

inductive iterates (f : α → α) : α → Prop where
  | step : iterates f x → iterates f (f x)
  | sup {c : α → Prop } (hc : chain c) (hi : ∀ x, c x → iterates f x) : iterates f (csup c)

def bot : α := csup (fun _ => False)

notation "⊥" => bot

theorem bot_le (x : α) : ⊥ ⊑ x := by
  apply csup_le
  · intro x y hx hy; contradiction
  · intro x hx; contradiction

theorem chain_iterates {f : α → α} (hf : monotone f) : chain (iterates f) := by
  intros x y hx hy
  induction hx generalizing y
  case step x hx ih =>
    induction hy
    case step y hy _ =>
      cases ih y hy
      · left; apply hf; assumption
      · right; apply hf; assumption
    case sup c hchain hi ih2 =>
      show f x ⊑ csup c ∨ csup c ⊑ f x
      by_cases h : ∃ z, c z ∧ f x ⊑ z
      · left
        obtain ⟨z, hz, hfz⟩ := h
        apply rel_trans hfz
        apply le_csup hchain hz
      · right
        apply csup_le hchain _
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
      apply le_csup hchain hz
    · left
      apply csup_le hchain _
      intro z hz
      rw [not_exists] at h
      specialize h z
      rw [not_and] at h
      specialize h hz
      cases ih z hz y hy
      next => assumption
      next => contradiction

theorem rel_f_of_iterates {f : α → α} (hf : monotone f) {x : α} (hx : iterates f x) : x ⊑ f x := by
  induction hx
  case step ih =>
    apply hf
    assumption
  case sup c hchain hi ih =>
    apply csup_le hchain
    intro y hy
    apply rel_trans (ih y hy)
    apply hf
    apply le_csup hchain hy

set_option linter.unusedVariables false in
-- We include hmono as an assumption already on the definition so that
-- we always have it available when applying `fix_eq`
def fix (f : α → α) (hmono : monotone f) := csup (iterates f)

theorem fix_eq {f : α → α} (hf : monotone f) : fix f hf = f (fix f hf) := by
  apply rel_antisymm
  · apply rel_f_of_iterates hf
    apply iterates.sup (chain_iterates hf)
    exact fun _ h => h
  · apply le_csup (chain_iterates hf)
    apply iterates.step
    apply iterates.sup (chain_iterates hf)
    intro y hy
    exact hy

end CCPO

section flat_order

variable {α : Type u}
variable [Nonempty α]

set_option linter.unusedVariables false in
def FlatOrder (α : Type u) [Nonempty α]:= α

noncomputable
def b : FlatOrder α := @Classical.ofNonempty α _

inductive FlatOrder.rel : (x y : FlatOrder α) → Prop where
  | bot : rel b x
  | refl : rel x x

instance FlatOrder.instOrder : Order (FlatOrder α) where
  rel := rel
  rel_refl := .refl
  rel_trans {x y z : α} (hxy : rel x y) (hyz : rel y z) := by
    cases hxy <;> cases hyz <;> constructor
  rel_antisymm {x y : α} (hxy : rel x y) (hyz : rel y x) : x = y := by
    cases hxy <;> cases hyz <;> constructor

open Classical in
private theorem Classical.some_spec₂ {α : Sort _} {p : α → Prop} {h : ∃ a, p a} (q : α → Prop)
    (hpq : ∀ a, p a → q a) : q (choose h) := hpq _ <| choose_spec _

noncomputable def flat_csup (c : FlatOrder α → Prop) : FlatOrder α := by
  by_cases h : ∃ (x : FlatOrder α), c x ∧ x ≠ b
  · exact Classical.choose h
  · exact b

noncomputable instance FlatOrder.instCCPO : CCPO (FlatOrder α) where
  csup := flat_csup
  csup_spec := by
    intro x c hc
    unfold flat_csup
    split
    next hex =>
      apply Classical.some_spec₂ (q := (· ⊑ x ↔ (∀ y, c y → y ⊑ x)))
      clear hex
      intro z ⟨hz, hnb⟩
      constructor
      · intro h y hy
        apply Order.rel_trans _ h; clear h
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
        suffices y = b by rw [this]; exact rel.bot
        rw [not_exists] at hnotex
        specialize hnotex y
        rw [not_and] at hnotex
        specialize hnotex hy
        rw [@Classical.not_not] at hnotex
        assumption
      · intro; exact rel.bot

end flat_order

section fun_order

open Order

variable {α : Type u}
variable {β : α → Type v}

instance instOrderPi [∀ x, Order (β x)] : Order (∀ x, β x) where
  rel f g := ∀ x, f x ⊑ g x
  rel_refl _ := rel_refl
  rel_trans hf hg x := rel_trans (hf x) (hg x)
  rel_antisymm hf hg := funext (fun x => rel_antisymm (hf x) (hg x))

theorem monotone_of_monotone_apply [Order γ] [∀ x, Order (β x)] (f : γ → (∀ x, β x))
  (h : ∀ y, monotone (fun x => f x y)) : monotone f :=
  fun x y hxy z => h z x y hxy

theorem monotone_apply [∀ x, Order (β x)] (x : α) :
    monotone (fun (f : (∀ x, β x)) => f x) := fun _ _ hfg => hfg x

/-
theorem cast_rel_cast' [∀ x, Order (β x)] {a b : α} (h : β a = β b) (x y : β a)
    (hfg : x ⊑ y) : (h ▸ x ⊑ h ▸ y) := sorry

theorem cast_rel_cast [∀ x, Order (β x)] {a b : α} (h : β a = β b) (f g : ∀ x, β x)
    (hfg : f a ⊑ g a) : (h ▸ f a ⊑ h ▸ g a) := cast_rel_cast' h (f a) (g a) hfg
-/

theorem chain_apply [∀ x, Order (β x)] {c : (∀ x, β x) → Prop} (hc : chain c) (x : α) :
    chain (fun y => ∃ f, c f ∧ f x = y) := by
  intro _ _ ⟨f, hf, hfeq⟩ ⟨g, hg, hgeq⟩
  subst hfeq; subst hgeq
  cases hc f g hf hg
  next h => left; apply h x
  next h => right; apply h x

def fun_csup  [∀ x, Order (β x)] [∀ x, CCPO (β x)] (c : (∀ x, β x) → Prop) (x : α) :=
  CCPO.csup (fun y => ∃ f, c f ∧ f x = y)

instance instCCPOPi [∀ x, Order (β x)] [∀ x, CCPO (β x)] : CCPO (∀ x, β x) where
  csup := fun_csup
  csup_spec := by
    intro f c hc
    constructor
    next =>
      intro hf g hg x
      apply rel_trans _ (hf x); clear hf
      apply le_csup (chain_apply hc x)
      exact ⟨g, hg, rfl⟩
    next =>
      intro h x
      apply csup_le (chain_apply hc x)
      intro y ⟨z, hz, hyz⟩
      subst y
      apply h z hz

end fun_order

/--
Variant of `fix` that hides the `Order` type classes. This is
used by the elaborator internally to ease the constrction, but unfolded before finishing
the construction.
-/
noncomputable
abbrev tailrec_fix
    {α : Type u}
    {β : α → Type v}
    [∀ x, Nonempty (β x)]
    (F : ∀ x, (∀ x, β x) → β x)
    (hmono : ∀ (x : α), monotone (α := ∀ x, FlatOrder (β x)) (β := FlatOrder (β _)) (fun f => F x f)) :
    (∀ x, β x) :=
  @fix (∀ x, FlatOrder (β x)) _ _ (fun f x => F x f)
    (monotone_of_monotone_apply (β := fun _ => FlatOrder _) (γ := ∀ _, FlatOrder _) _ hmono)

namespace Example

def findF (P : Nat → Bool) (rec : Nat → Option Nat) (x : Nat) : Option Nat :=
  if P x then
    some x
  else
    rec (x + 1)

noncomputable def find P := fix (α := _ → FlatOrder _) (findF P) <| by
  unfold findF
  apply monotone_of_monotone_apply (β := fun _ => FlatOrder _)
  intro n
  split
  · apply monotone_const
  · apply monotone_apply

theorem find_eq : find P = findF P (find P) := fix_eq ..

end Example

end Lean.Tailrec
