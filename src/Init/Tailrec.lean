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

def fix (f : α → α) := csup (iterates f)

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

theorem fix_eq {f : α → α} (hf : monotone f) : fix f = f (fix f) := by
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

instance [∀ x, Order (β x)] : Order (∀ x, β x) where
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

instance [∀ x, Order (β x)] [∀ x, CCPO (β x)] : CCPO (∀ x, β x) where
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

section tailrec

variable {α : Type u}
variable {β : α → Type v}
variable {γ : Type w}
variable [∀ x, Nonempty (β x)]
variable [Nonempty γ]

def mono (F : (∀ x, β x) → γ) :=
    monotone (α := ∀ x, FlatOrder (β x)) (β := FlatOrder γ) F

theorem mono_const (c : γ) : mono fun (_ : (∀ x, β x)) => c :=
  monotone_const _

theorem mono_apply : mono fun (f : (∀ x, β x)) => f x :=
  monotone_apply (β := fun _ => FlatOrder _) x

theorem mono_psigma_casesOn.{ww,uu,vv}
    {δ : Sort uu} {ε : δ → Sort vv}
    {γ : PSigma ε → Type ww}
    (p : PSigma ε)
    [Nonempty (γ p)]
    (k : (∀ x, β x) → (a : δ) → (b : ε a) → γ ⟨a, b⟩)
    (hmono : ∀ a b [Nonempty (γ ⟨a,b⟩)], mono fun (f : (∀ x, β x)) => k f a b) :
  mono fun (f : (∀ x, β x)) => PSigma.casesOn (motive := γ) p (k f) := by
    cases p; apply hmono

theorem mono_psum_casesOn.{ww,uu,vv}
    {δ : Sort uu} {ε : Sort vv}
    {γ : δ ⊕' ε -> Type ww}
    (p : δ ⊕' ε)
    [Nonempty (γ p)]
    (k₁ : (∀ x, β x) → (a : δ) → γ (.inl a))
    (k₂ : (∀ x, β x) → (b : ε) → γ (.inr b))
    (hmono₁ : ∀ a [Nonempty (γ (.inl a))], mono fun (f : (∀ x, β x)) => k₁ f a)
    (hmono₂ : ∀ b [Nonempty (γ (.inr b))], mono fun (f : (∀ x, β x)) => k₂ f b) :
    mono (γ := γ p) fun (f : (∀ x, β x)) =>
      PSum.casesOn (motive := γ) p (k₁ f) (k₂ f) := by
    cases p
    · apply hmono₁
    · apply hmono₂

theorem mono_ite
  (c : Prop) [Decidable c]
  (k₁ : (∀ x, β x) → γ)
  (k₂ : (∀ x, β x) → γ)
  (hmono₁ : mono (fun f => k₁ f))
  (hmono₂ : mono (fun f => k₂ f)) :
  mono fun f => if c then k₁ f else k₂ f := by
    split
    · apply hmono₁
    · apply hmono₂

theorem mono_dite
  (c : Prop) [Decidable c]
  (k₁ : (∀ x, β x) → c → γ)
  (k₂ : (∀ x, β x) → ¬ c → γ)
  (hmono₁ : (h : c) → mono (fun f => k₁ f h))
  (hmono₂ : (h : ¬ c) → mono (fun f => k₂ f h)) :
  mono fun f => dite c (k₁ f) (k₂ f) := by
    split
    · apply hmono₁
    · apply hmono₂

set_option linter.unusedVariables false in
/--
Variant of `fix` that hides the `Order` type classes, and reorders
the arguments to `F`.
-/
noncomputable
def tailrec_fix
    (F : ∀ x, (∀ x, β x) → β x)
    (hmono : ∀ (x : α), mono (fun f => F x f)) : (∀ x, β x) :=
  @fix (∀ x, FlatOrder (β x)) _ _ (fun f x => F x f)

theorem tailrec_fix_eq
    (F : ∀ x, (∀ x, β x) → β x)
    (hmono : ∀ (x : α), mono (fun f => F x f))
    (x : α) :
    tailrec_fix F hmono x = F x (tailrec_fix F hmono) :=
  congrFun
    (@fix_eq (∀ _, FlatOrder _) _ _ (fun f x => F x f)
      (monotone_of_monotone_apply (β := fun _ => FlatOrder _) (γ := ∀ _, FlatOrder _) _ hmono)
    ) x

end tailrec

namespace Example

def findF (P : Nat → Bool)  (x : Nat) (rec : Nat → Option Nat) : Option Nat :=
  if P x then
    some x
  else
    rec (x +1)

noncomputable def find P := tailrec_fix (findF P) <| by
  unfold findF
  intro n
  split
  · apply mono_const
  · apply mono_apply

theorem find_eq : find P x = findF P x (find P) := tailrec_fix_eq ..

end Example

end Lean.Tailrec
