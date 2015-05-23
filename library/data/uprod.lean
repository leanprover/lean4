/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Unordered pairs
-/
import data.prod logic.identities algebra.function
open prod prod.ops quot function

private definition eqv {A : Type} (p₁ p₂ : A × A) : Prop :=
p₁ = p₂ ∨ swap p₁ = p₂

infix `~` := eqv    -- this is "~"

private theorem eqv.refl [refl] {A : Type} : ∀ p : A × A, p ~ p :=
take p, or.inl rfl

private theorem eqv.symm [symm] {A : Type} : ∀ p₁ p₂ : A × A, p₁ ~ p₂ → p₂ ~ p₁ :=
take p₁ p₂ h, or.elim h
  (λ e, by rewrite e)
  (λ e, begin esimp [eqv], rewrite [-e, swap_swap], right, reflexivity end)

private theorem eqv.trans [trans] {A : Type} : ∀ p₁ p₂ p₃ : A × A, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃ :=
take p₁ p₂ p₃ h₁ h₂, or.elim h₁
  (λ e₁₂,  or.elim h₂
    (λ e₂₃,  by rewrite [e₁₂, e₂₃])
    (λ es₂₃, begin esimp [eqv], rewrite -es₂₃, right, congruence, assumption end))
  (λ es₁₂, or.elim h₂
    (λ e₂₃,  begin esimp [eqv], rewrite es₁₂, right, assumption end)
    (λ es₂₃, begin esimp [eqv], rewrite [-es₁₂ at es₂₃, swap_swap at es₂₃], left, assumption end))

private theorem is_equivalence (A : Type) : equivalence (@eqv A) :=
mk_equivalence (@eqv A) (@eqv.refl A) (@eqv.symm A) (@eqv.trans A)

definition uprod.setoid [instance] (A : Type) : setoid (A × A) :=
setoid.mk (@eqv A) (is_equivalence A)

definition uprod (A : Type) : Type :=
quot (uprod.setoid A)

namespace uprod
  definition mk {A : Type} (a b : A) : uprod A :=
  ⟦(a, b)⟧

  theorem mk_eq_mk {A : Type} (a b : A) : mk a b = mk b a :=
  quot.sound (or.inr rfl)

  private definition mem_fn {A : Type} (a : A) : A × A → Prop
  | (a₁, a₂) := a = a₁ ∨ a = a₂

  private lemma mem_swap {A : Type} {a : A} : ∀ {p : A × A}, mem_fn a p ↔ mem_fn a (swap p)
  | (a₁, a₂) := iff.intro
    (λ l : a = a₁ ∨ a = a₂, or.swap l)
    (λ r : a = a₂ ∨ a = a₁, or.swap r)

  private lemma mem_coherent {A : Type} : ∀ {p₁ p₂ : A × A} (a : A),  p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, b₁) (a₂, b₂) a h :=
    or.elim h
     (λ e,  by rewrite e)
     (λ es, begin rewrite -es, apply propext, rewrite (propext mem_swap) end)

  definition mem {A : Type} (a : A) (u : uprod A) : Prop :=
  quot.lift_on u (λ p, mem_fn a p) (λ p₁ p₂ e, mem_coherent a e)

  infix `∈` := mem

  theorem mem_mk_left {A : Type} (a b : A) : a ∈ mk a b :=
  or.inl rfl

  theorem mem_mk_right {A : Type} (a b : A) : b ∈ mk a b :=
  or.inr rfl

  theorem mem_or_mem_of_mem_mk {A : Type} {a b c : A} : c ∈ mk a b → c = a ∨ c = b :=
  λ h, h

  private definition map_fn {A B : Type} (f : A → B) : A × A → uprod B
  | (a₁, a₂) := mk (f a₁) (f a₂)

  private lemma map_coherent {A B : Type} (f : A → B) : ∀ {p₁ p₂ : A × A}, p₁ ~ p₂ → map_fn f p₁ = map_fn f p₂
  | (a₁, b₁) (a₂, b₂) h :=
    or.elim h
      (λ e,  by rewrite e)
      (λ es, begin rewrite -es, apply quot.sound, right, reflexivity end)

  definition map {A B : Type} (f : A → B) (u : uprod A) : uprod B :=
  quot.lift_on u (λ p, map_fn f p) (λ p₁ p₂ c, map_coherent f c)

  theorem mem_map_mk_left {A B : Type} (f : A → B) (a₁ a₂ : A) : f a₁ ∈ map f (mk a₁ a₂) :=
  or.inl rfl

  theorem mem_map_mk_right {A B : Type} (f : A → B) (a₁ a₂ : A) : f a₂ ∈ map f (mk a₁ a₂) :=
  or.inr rfl

  theorem map_map {A B C : Type} (g : B → C) (f : A → B) (u : uprod A) : map g (map f u) = map (g ∘ f) u :=
  quot.induction_on u (λ p : A × A, begin cases p, reflexivity end)
end uprod
