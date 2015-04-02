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

variables {A B : Type} (R : B → B → Prop)
local infix `≺`:50 := R

definition reflexive := ∀x, x ≺ x

definition symmetric := ∀⦃x y⦄, x ≺ y → y ≺ x

definition transitive := ∀⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

definition equivalence := reflexive R ∧ symmetric R ∧ transitive R

definition mk_equivalence (r : reflexive R) (s : symmetric R) (t : transitive R) : equivalence R :=
and.intro r (and.intro s t)

definition irreflexive := ∀x, ¬ x ≺ x

definition anti_symmetric := ∀⦃x y⦄, x ≺ y → y ≺ x → x = y

definition empty_relation := λa₁ a₂ : A, false

definition subrelation (Q R : B → B → Prop) := ∀⦃x y⦄, Q x y → R x y

definition inv_image (f : A → B) : A → A → Prop :=
λa₁ a₂, f a₁ ≺ f a₂

theorem inv_image.trans (f : A → B) (H : transitive R) : transitive (inv_image R f) :=
λ (a₁ a₂ a₃ : A) (H₁ : inv_image R f a₁ a₂) (H₂ : inv_image R f a₂ a₃), H H₁ H₂

theorem inv_image.irreflexive (f : A → B) (H : irreflexive R) : irreflexive (inv_image R f) :=
λ (a : A) (H₁ : inv_image R f a a), H (f a) H₁

inductive tc {A : Type} (R : A → A → Prop) : A → A → Prop :=
| base  : ∀a b, R a b → tc R a b
| trans : ∀a b c, tc R a b → tc R b c → tc R a c
