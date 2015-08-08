/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Complete lattices
-/
import algebra.lattice data.set
open set

namespace algebra

variable {A : Type}

structure complete_lattice [class] (A : Type) extends lattice A :=
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

end complete_lattice
end algebra
