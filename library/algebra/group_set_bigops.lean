/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Set-based version of group_bigops.
-/
import .group_bigops data.set.finite
open set classical

namespace algebra
namespace set

variables {A B : Type}

/- Prod: product indexed by a set -/

section Prod
  variable [cmB : comm_monoid B]
  include cmB

  noncomputable definition Prod (s : set A) (f : A → B) : B := algebra.finset.Prod (to_finset s) f

  -- ∏ x ∈ s, f x
  notation `∏` binders `∈` s, r:(scoped f, prod s f) := r

  theorem Prod_empty (f : A → B) : Prod ∅ f = 1 :=
  by rewrite [↑Prod, to_finset_empty]

  theorem Prod_of_not_finite {s : set A} (nfins : ¬ finite s) (f : A → B) : Prod s f = 1 :=
  by rewrite [↑Prod, to_finset_of_not_finite nfins]

  theorem Prod_mul (s : set A) (f g : A → B) : Prod s (λx, f x * g x) = Prod s f * Prod s g :=
  by rewrite [↑Prod, finset.Prod_mul]

  theorem Prod_insert_of_mem (f : A → B) {a : A} {s : set A} (H : a ∈ s) :
    Prod (insert a s) f = Prod s f :=
  by_cases
    (suppose finite s,
      assert (#finset a ∈ set.to_finset s), by rewrite mem_to_finset_eq; apply H,
      by rewrite [↑Prod, to_finset_insert, finset.Prod_insert_of_mem f this])
    (assume nfs : ¬ finite s,
      assert ¬ finite (insert a s), from assume H, nfs (finite_of_finite_insert H),
      by rewrite [Prod_of_not_finite nfs, Prod_of_not_finite this])

  theorem Prod_insert_of_not_mem (f : A → B) {a : A} {s : set A} [fins : finite s] (H : a ∉ s) :
    Prod (insert a s) f = f a * Prod s f :=
  assert (#finset a ∉ set.to_finset s), by rewrite mem_to_finset_eq; apply H,
  by rewrite [↑Prod, to_finset_insert, finset.Prod_insert_of_not_mem f this]

  theorem Prod_union (f : A → B) {s₁ s₂ : set A} [fins₁ : finite s₁] [fins₂ : finite s₂]
      (disj : s₁ ∩ s₂ = ∅) :
    Prod (s₁ ∪ s₂) f = Prod s₁ f * Prod s₂ f :=
  begin
    rewrite [↑Prod, to_finset_union],
    apply finset.Prod_union,
    apply finset.eq_of_to_set_eq_to_set,
    rewrite [finset.to_set_inter, *to_set_to_finset, finset.to_set_empty, disj]
  end

  theorem Prod_ext {s : set A} {f g : A → B} (H : ∀{x}, x ∈ s → f x = g x) : Prod s f = Prod s g :=
  by_cases
    (suppose finite s,
      by esimp [Prod]; apply finset.Prod_ext; intro x; rewrite [mem_to_finset_eq]; apply H)
    (assume nfs : ¬ finite s,
      by rewrite [*Prod_of_not_finite nfs])

  theorem Prod_one (s : set A) : Prod s (λ x, 1) = (1:B) :=
  by rewrite [↑Prod, finset.Prod_one]
end Prod

/- Sum -/

section Sum
  variable [acmB : add_comm_monoid B]
  include acmB
  local attribute add_comm_monoid.to_comm_monoid [trans_instance]

  noncomputable definition Sum (s : set A) (f : A → B) : B := Prod s f

  -- ∑ x ∈ s, f x
  notation `∑` binders `∈` s, r:(scoped f, Sum s f) := r

  theorem Sum_empty (f : A → B) : Sum ∅ f = 0 := Prod_empty f
  theorem Sum_of_not_finite {s : set A} (nfins : ¬ finite s) (f : A → B) : Sum s f = 0 :=
    Prod_of_not_finite nfins f
  theorem Sum_add (s : set A) (f g : A → B) :
    Sum s (λx, f x + g x) = Sum s f + Sum s g := Prod_mul s f g

  theorem Sum_insert_of_mem (f : A → B) {a : A} {s : set A} (H : a ∈ s) :
    Sum (insert a s) f = Sum s f := Prod_insert_of_mem f H
  theorem Sum_insert_of_not_mem (f : A → B) {a : A} {s : set A} [fins : finite s] (H : a ∉ s) :
    Sum (insert a s) f = f a + Sum s f := Prod_insert_of_not_mem f H
  theorem Sum_union (f : A → B) {s₁ s₂ : set A} [fins₁ : finite s₁] [fins₂ : finite s₂]
      (disj : s₁ ∩ s₂ = ∅) :
    Sum (s₁ ∪ s₂) f = Sum s₁ f + Sum s₂ f := Prod_union f disj
  theorem Sum_ext {s : set A} {f g : A → B} (H : ∀x, x ∈ s → f x = g x) :
    Sum s f = Sum s g := Prod_ext H

  theorem Sum_zero (s : set A) : Sum s (λ x, 0) = (0:B) := Prod_one s
end Sum

end set


end algebra
