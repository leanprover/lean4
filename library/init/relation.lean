/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module init.relation
Authors: Leonardo de Moura
-/
prelude
import init.logic

-- TODO(Leo): remove duplication between this file and algebra/relation.lean
-- We need some of the following definitions asap when "initializing" Lean.
universe variables u v
variables {A : Type u} {B : Type v} (R : B → B → Prop)
local infix `≺`:50 := R

def reflexive := ∀ x, x ≺ x

def symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

def transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

def equivalence := reflexive R ∧ symmetric R ∧ transitive R

def total := ∀ x y, x ≺ y ∨ y ≺ x

def mk_equivalence (r : reflexive R) (s : symmetric R) (t : transitive R) : equivalence R :=
⟨r, s, t⟩

def irreflexive := ∀ x, ¬ x ≺ x

def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

def empty_relation := λ a₁ a₂ : A, false

def subrelation (Q R : B → B → Prop) := ∀ ⦃x y⦄, Q x y → R x y

def inv_image (f : A → B) : A → A → Prop :=
λ a₁ a₂, f a₁ ≺ f a₂

lemma inv_image.trans (f : A → B) (H : transitive R) : transitive (inv_image R f) :=
λ (a₁ a₂ a₃ : A) (H₁ : inv_image R f a₁ a₂) (H₂ : inv_image R f a₂ a₃), H H₁ H₂

lemma inv_image.irreflexive (f : A → B) (H : irreflexive R) : irreflexive (inv_image R f) :=
λ (a : A) (H₁ : inv_image R f a a), H (f a) H₁

inductive tc {A : Type u} (R : A → A → Prop) : A → A → Prop
| base  : ∀ a b, R a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c
