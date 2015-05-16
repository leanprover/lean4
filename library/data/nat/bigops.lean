/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Finite products and sums on the natural numbers.
-/
import data.nat.basic data.nat.order algebra.group_bigops
open list

namespace nat
  open [classes] algebra
  local attribute nat.comm_semiring [instance]
  variable {A : Type}

  /- list.prod and list.sum -/

  definition list.prod (l : list A) (f : A → nat) : nat := algebra.list.prod l f
  notation `∏` binders `←` l, r:(scoped f, list.prod l f) := r
  definition list.sum (l : list A) (f : A → nat) : nat := algebra.list.sum l f
  notation `∑` binders `←` l, r:(scoped f, list.sum l f) := r

  namespace list -- i.e. nat.list
  open list      -- i.e. ordinary lists

  theorem prod_nil (f : A → nat) : prod [] f = 1 := algebra.list.prod_nil f
  theorem prod_cons (f : A → nat) (a : A) (l : list A) : prod (a::l) f = f a * prod l f :=
    algebra.list.prod_cons f a l
  theorem prod_append (l₁ l₂ : list A) (f : A → nat) : prod (l₁++l₂) f = prod l₁ f * prod l₂ f :=
    algebra.list.prod_append l₁ l₂ f
  section decidable_eq
    variable [H : decidable_eq A]
    include H
    theorem prod_insert_of_mem (f : A → nat) {a : A} {l : list A} (H : a ∈ l) :
      prod (insert a l) f = prod l f := algebra.list.prod_insert_of_mem f H
    theorem prod_insert_of_not_mem (f : A → nat) {a : A} {l : list A} (H : a ∉ l) :
      prod (insert a l) f = f a * prod l f := algebra.list.prod_insert_of_not_mem f H
    theorem prod_union {l₁ l₂ : list A} (f : A → nat) (d : disjoint l₁ l₂) :
      prod (union l₁ l₂) f = prod l₁ f * prod l₂ f := algebra.list.prod_union f d
  end decidable_eq
  theorem prod_mul (l : list A) (f g : A → nat) :
    prod l (λx, f x * g x) = prod l f * prod l g := algebra.list.prod_mul l f g

  theorem sum_nil (f : A → nat) : sum [] f = 0 := algebra.list.sum_nil f
  theorem sum_cons (f : A → nat) (a : A) (l : list A) : sum (a::l) f = f a + sum l f :=
    algebra.list.sum_cons f a l
  theorem sum_append (l₁ l₂ : list A) (f : A → nat) : sum (l₁++l₂) f = sum l₁ f + sum l₂ f :=
    algebra.list.sum_append l₁ l₂ f
  section decidable_eq
    variable [H : decidable_eq A]
    include H
    theorem sum_insert_of_mem (f : A → nat) {a : A} {l : list A} (H : a ∈ l) :
      sum (insert a l) f = sum l f := algebra.list.sum_insert_of_mem f H
    theorem sum_insert_of_not_mem (f : A → nat) {a : A} {l : list A} (H : a ∉ l) :
      sum (insert a l) f = f a + sum l f := algebra.list.sum_insert_of_not_mem f H
    theorem sum_union {l₁ l₂ : list A} (f : A → nat) (d : disjoint l₁ l₂) :
      sum (union l₁ l₂) f = sum l₁ f + sum l₂ f := algebra.list.sum_union f d
  end decidable_eq
  theorem sum_add (l : list A) (f g : A → nat) : sum l (λx, f x + g x) = sum l f + sum l g :=
    algebra.list.sum_add l f g
  end list

  /- finset.prod and finset.sum -/

  definition finset.prod (s : finset A) (f : A → nat) : nat := algebra.finset.prod s f
  notation `∏` binders `∈` s, r:(scoped f, finset.prod s f) := r
  definition finset.sum (s : finset A) (f : A → nat) : nat := algebra.finset.sum s f
  notation `∑` binders `∈` s, r:(scoped f, finset.sum s f) := r

  namespace finset
  open finset
  theorem prod_empty (f : A → nat) : finset.prod ∅ f = 1 := algebra.finset.prod_empty f
  section decidable_eq
    variable [H : decidable_eq A]
    include H
    theorem prod_insert_of_mem (f : A → nat) {a : A} {s : finset A} (H : a ∈ s) :
      prod (insert a s) f = prod s f := algebra.finset.prod_insert_of_mem f H
    theorem prod_insert_of_not_mem (f : A → nat) {a : A} {s : finset A} (H : a ∉ s) :
      prod (insert a s) f = f a * prod s f := algebra.finset.prod_insert_of_not_mem f H
    theorem prod_union (f : A → nat) {s₁ s₂ : finset A} (disj : s₁ ∩ s₂ = ∅) :
      prod (s₁ ∪ s₂) f = prod s₁ f * prod s₂ f := algebra.finset.prod_union f disj
  end decidable_eq
  theorem prod_mul (s : finset A) (f g : A → nat) : prod s (λx, f x * g x) = prod s f * prod s g :=
    algebra.finset.prod_mul s f g

  theorem sum_empty (f : A → nat) : finset.sum ∅ f = 0 := algebra.finset.sum_empty f
  section decidable_eq
    variable [H : decidable_eq A]
    include H
    theorem sum_insert_of_mem (f : A → nat) {a : A} {s : finset A} (H : a ∈ s) :
      sum (insert a s) f = sum s f := algebra.finset.sum_insert_of_mem f H
    theorem sum_insert_of_not_mem (f : A → nat) {a : A} {s : finset A} (H : a ∉ s) :
      sum (insert a s) f = f a + sum s f := algebra.finset.sum_insert_of_not_mem f H
    theorem sum_union (f : A → nat) {s₁ s₂ : finset A} (disj : s₁ ∩ s₂ = ∅) :
      sum (s₁ ∪ s₂) f = sum s₁ f + sum s₂ f := algebra.finset.sum_union f disj
  end decidable_eq
  theorem sum_add (s : finset A) (f g : A → nat) : sum s (λx, f x + g x) = sum s f + sum s g :=
    algebra.finset.sum_add s f g
  end finset
end nat
