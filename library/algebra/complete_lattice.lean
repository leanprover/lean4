/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Complete lattices

TODO: define dual complete lattice and simplify proof of dual theorems.
-/
import algebra.lattice data.set
open set

namespace algebra

variable {A : Type}

structure complete_lattice [class] (A : Type) extends weak_order A :=
(Inf : set A → A)
(Inf_le : ∀ {a : A} {s : set A}, a ∈ s → le (Inf s) a)
(le_Inf : ∀ {b : A} {s : set A}, (∀ (a : A), a ∈ s → le b a) → le b (Inf s))

namespace complete_lattice
variable [C : complete_lattice A]
include C

definition Sup (s : set A) : A :=
Inf {b | ∀ a, a ∈ s → a ≤ b}

prefix `⨅`:70 := Inf
prefix `⨆`:65 := Sup

lemma le_Sup {a : A} {s : set A} : a ∈ s → a ≤ ⨆ s :=
suppose a ∈ s, le_Inf
  (show ∀ (b : A), (∀ (a : A), a ∈ s → a ≤ b) → a ≤ b, from
   take b, assume h, h a `a ∈ s`)

lemma Sup_le {b : A} {s : set A} (h : ∀ (a : A), a ∈ s → a ≤ b) : ⨆ s ≤ b :=
Inf_le h

definition inf (a b : A) := ⨅ '{a, b}
definition sup (a b : A) := ⨆ '{a, b}
infix `⊓` := inf
infix `⊔` := sup

lemma inf_le_left (a b : A) : a ⊓ b ≤ a :=
Inf_le !mem_insert

lemma inf_le_right (a b : A) : a ⊓ b ≤ b :=
Inf_le (!mem_insert_of_mem !mem_insert)

lemma le_inf {a b c : A} : c ≤ a → c ≤ b → c ≤ a ⊓ b :=
assume h₁ h₂,
le_Inf (take x, suppose x ∈ '{a, b},
  or.elim (eq_or_mem_of_mem_insert this)
    (suppose x = a, by subst x; assumption)
    (suppose x ∈ '{b},
      assert x = b, from !eq_of_mem_singleton this,
      by subst x; assumption))

lemma le_sup_left (a b : A) : a ≤ a ⊔ b :=
le_Sup !mem_insert

lemma le_sup_right (a b : A) : b ≤ a ⊔ b :=
le_Sup (!mem_insert_of_mem !mem_insert)

lemma sup_le {a b c : A} : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
assume h₁ h₂,
Sup_le (take x, suppose x ∈ '{a, b},
  or.elim (eq_or_mem_of_mem_insert this)
    (suppose x = a, by subst x; assumption)
    (suppose x ∈ '{b},
      assert x = b, from !eq_of_mem_singleton this,
      by subst x; assumption))

definition complete_lattice_is_lattice [instance] : lattice A :=
⦃ lattice, C,
  inf := inf,
  sup := sup,
  inf_le_left  := inf_le_left,
  inf_le_right := inf_le_right,
  le_inf       := @le_inf A C,
  le_sup_left  := le_sup_left,
  le_sup_right := le_sup_right,
  sup_le       := @sup_le A C ⦄

variable {f : A → A}
premise  (mono : ∀ x y : A, x ≤ y → f x ≤ f y)

theorem knaster_tarski : ∃ a, f a = a ∧ ∀ b, f b = b → a ≤ b :=
let a := ⨅ {u | f u ≤ u} in
have h₁ : f a = a, from
  have ge : f a ≤ a, from
    have ∀ b, b ∈ {u | f u ≤ u} → f a ≤ b, from
      take b, suppose f b ≤ b,
      have a ≤ b,     from Inf_le this,
      have f a ≤ f b, from !mono this,
      le.trans `f a ≤ f b` `f b ≤ b`,
    le_Inf this,
  have le : a ≤ f a, from
    have f (f a) ≤ f a,  from !mono ge,
    have f a ∈ {u | f u ≤ u}, from this,
    Inf_le this,
  le.antisymm ge le,
have h₂ : ∀ b, f b = b → a ≤ b, from
  take b,
  suppose f b = b,
  have b ∈ {u | f u ≤ u}, from
    show f b ≤ b, by rewrite this; apply le.refl,
  Inf_le this,
exists.intro a (and.intro h₁ h₂)

theorem knaster_tarski_dual : ∃ a, f a = a ∧ ∀ b, f b = b → b ≤ a :=
let a := ⨆ {u | u ≤ f u} in
have h₁ : f a = a, from
  have le : a ≤ f a, from
    have ∀ b, b ∈ {u | u ≤ f u} → b ≤ f a, from
      take b, suppose b ≤ f b,
      have b ≤ a,     from le_Sup this,
      have f b ≤ f a, from !mono this,
      le.trans `b ≤ f b` `f b ≤ f a`,
    Sup_le this,
  have ge : f a ≤ a, from
    have f a ≤ f (f a),  from !mono le,
    have f a ∈ {u | u ≤ f u}, from this,
    le_Sup this,
  le.antisymm ge le,
have h₂ : ∀ b, f b = b → b ≤ a, from
  take b,
  suppose f b = b,
  have b ≤ f b, by rewrite this; apply le.refl,
  le_Sup this,
exists.intro a (and.intro h₁ h₂)

definition bot : A := ⨅ univ
definition top : A := ⨆ univ
notation `⊥` := bot
notation `⊤` := top

lemma bot_le (a : A) : ⊥ ≤ a :=
Inf_le !mem_univ

lemma eq_bot {a : A} : (∀ b, a ≤ b) → a = ⊥ :=
assume h,
have a ≤ ⊥, from le_Inf (take b bin, h b),
le.antisymm this !bot_le

lemma le_top (a : A) : a ≤ ⊤ :=
le_Sup !mem_univ

lemma eq_top {a : A} : (∀ b, b ≤ a) → a = ⊤ :=
assume h,
have ⊤ ≤ a, from Sup_le (take b bin, h b),
le.antisymm !le_top this

lemma Inf_singleton {a : A} : ⨅'{a} = a :=
have ⨅'{a} ≤ a, from
  Inf_le !mem_insert,
have a ≤ ⨅'{a}, from
  le_Inf (take b, suppose b ∈ '{a}, assert b = a, from eq_of_mem_singleton this, by rewrite this; apply le.refl),
le.antisymm `⨅'{a} ≤ a` `a ≤ ⨅'{a}`

lemma Sup_singleton {a : A} : ⨆'{a} = a :=
have ⨆'{a} ≤ a, from
  Sup_le (take b, suppose b ∈ '{a}, assert b = a, from eq_of_mem_singleton this, by rewrite this; apply le.refl),
have a ≤ ⨆'{a}, from
  le_Sup !mem_insert,
le.antisymm `⨆'{a} ≤ a` `a ≤ ⨆'{a}`

lemma Inf_antimono {s₁ s₂ : set A} : s₁ ⊆ s₂ → ⨅ s₂ ≤ ⨅ s₁ :=
suppose s₁ ⊆ s₂, le_Inf (take a : A, suppose a ∈ s₁, Inf_le (mem_of_subset_of_mem `s₁ ⊆ s₂` `a ∈ s₁`))

lemma Sup_mono {s₁ s₂ : set A} : s₁ ⊆ s₂ → ⨆ s₁ ≤ ⨆ s₂ :=
suppose s₁ ⊆ s₂, Sup_le (take a : A, suppose a ∈ s₁, le_Sup (mem_of_subset_of_mem `s₁ ⊆ s₂` `a ∈ s₁`))

lemma Inf_union (s₁ s₂ : set A) : ⨅ (s₁ ∪ s₂) = (⨅s₁) ⊓ (⨅s₂) :=
have le₁ : ⨅ (s₁ ∪ s₂) ≤ (⨅s₁) ⊓ (⨅s₂), from
  le_inf
    (le_Inf (take a : A, suppose a ∈ s₁, Inf_le (mem_union_of_mem_left _ `a ∈ s₁`)))
    (le_Inf (take a : A, suppose a ∈ s₂, Inf_le (mem_union_of_mem_right _ `a ∈ s₂`))),
have le₂ : (⨅s₁) ⊓ (⨅s₂) ≤ ⨅ (s₁ ∪ s₂), from
  le_Inf (take a : A, suppose a ∈ s₁ ∪ s₂,
    or.elim this
      (suppose a ∈ s₁,
        have (⨅s₁) ⊓ (⨅s₂) ≤ ⨅s₁, from !inf_le_left,
        have ⨅s₁ ≤ a, from Inf_le `a ∈ s₁`,
        le.trans `(⨅s₁) ⊓ (⨅s₂) ≤ ⨅s₁` `⨅s₁ ≤ a`)
      (suppose a ∈ s₂,
        have (⨅s₁) ⊓ (⨅s₂) ≤ ⨅s₂, from !inf_le_right,
        have ⨅s₂ ≤ a, from Inf_le `a ∈ s₂`,
        le.trans `(⨅s₁) ⊓ (⨅s₂) ≤ ⨅s₂` `⨅s₂ ≤ a`)),
le.antisymm le₁ le₂

lemma Sup_union (s₁ s₂ : set A) : ⨆ (s₁ ∪ s₂) = (⨆s₁) ⊔ (⨆s₂) :=
have le₁ : ⨆ (s₁ ∪ s₂) ≤ (⨆s₁) ⊔ (⨆s₂), from
  Sup_le (take a : A, suppose a ∈ s₁ ∪ s₂,
    or.elim this
      (suppose a ∈ s₁,
        have a ≤ ⨆s₁, from le_Sup `a ∈ s₁`,
        have ⨆s₁ ≤ (⨆s₁) ⊔ (⨆s₂), from !le_sup_left,
        le.trans `a ≤ ⨆s₁` `⨆s₁ ≤ (⨆s₁) ⊔ (⨆s₂)`)
      (suppose a ∈ s₂,
        have a ≤ ⨆s₂, from le_Sup `a ∈ s₂`,
        have ⨆s₂ ≤ (⨆s₁) ⊔ (⨆s₂), from !le_sup_right,
        le.trans `a ≤ ⨆s₂` `⨆s₂ ≤ (⨆s₁) ⊔ (⨆s₂)`)),
have le₂ : (⨆s₁) ⊔ (⨆s₂) ≤ ⨆ (s₁ ∪ s₂), from
  sup_le
    (Sup_le (take a : A, suppose a ∈ s₁, le_Sup (mem_union_of_mem_left _ `a ∈ s₁`)))
    (Sup_le (take a : A, suppose a ∈ s₂, le_Sup (mem_union_of_mem_right _ `a ∈ s₂`))),
le.antisymm le₁ le₂

lemma Inf_empty_eq_Sup_univ : ⨅ (∅ : set A) = ⨆ univ :=
have le₁ : ⨅ ∅ ≤ ⨆ univ, from
  le_Sup !mem_univ,
have le₂ : ⨆ univ ≤ ⨅ ∅, from
  le_Inf (take a, suppose a ∈ ∅, absurd this !not_mem_empty),
le.antisymm le₁ le₂

lemma Sup_empty_eq_Inf_univ : ⨆ (∅ : set A) = ⨅ univ :=
have le₁ : ⨆ (∅ : set A) ≤ ⨅ univ, from
  Sup_le (take a, suppose a ∈ ∅, absurd this !not_mem_empty),
have le₂ : ⨅ univ ≤ ⨆ (∅ : set A), from
  Inf_le !mem_univ,
le.antisymm le₁ le₂

end complete_lattice
end algebra
