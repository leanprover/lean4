/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Finite products and sums on the integers.
-/
import data.int.order algebra.group_bigops algebra.group_set_bigops
open list

namespace int
open [classes] algebra
local attribute int.decidable_linear_ordered_comm_ring [instance]
variables {A : Type} [deceqA : decidable_eq A]

/- Prodl -/

definition Prodl (l : list A) (f : A → int) : int := algebra.Prodl l f
notation `∏` binders `←` l, r:(scoped f, Prodl l f) := r

theorem Prodl_nil (f : A → int) : Prodl [] f = 1 := algebra.Prodl_nil f
theorem Prodl_cons (f : A → int) (a : A) (l : list A) : Prodl (a::l) f = f a * Prodl l f :=
  algebra.Prodl_cons f a l
theorem Prodl_append (l₁ l₂ : list A) (f : A → int) : Prodl (l₁++l₂) f = Prodl l₁ f * Prodl l₂ f :=
  algebra.Prodl_append l₁ l₂ f
theorem Prodl_mul (l : list A) (f g : A → int) :
  Prodl l (λx, f x * g x) = Prodl l f * Prodl l g := algebra.Prodl_mul l f g
section deceqA
  include deceqA
  theorem Prodl_insert_of_mem (f : A → int) {a : A} {l : list A} (H : a ∈ l) :
    Prodl (insert a l) f = Prodl l f := algebra.Prodl_insert_of_mem f H
  theorem Prodl_insert_of_not_mem (f : A → int) {a : A} {l : list A} (H : a ∉ l) :
    Prodl (insert a l) f = f a * Prodl l f := algebra.Prodl_insert_of_not_mem f H
  theorem Prodl_union {l₁ l₂ : list A} (f : A → int) (d : disjoint l₁ l₂) :
    Prodl (union l₁ l₂) f = Prodl l₁ f * Prodl l₂ f := algebra.Prodl_union f d
  theorem Prodl_one (l : list A) : Prodl l (λ x, 1) = 1 := algebra.Prodl_one l
end deceqA

/- Prod over finset -/

namespace finset
open finset

definition Prod (s : finset A) (f : A → int) : int := algebra.finset.Prod s f
notation `∏` binders `∈` s, r:(scoped f, Prod s f) := r

theorem Prod_empty (f : A → int) : Prod ∅ f = 1 := algebra.finset.Prod_empty f
theorem Prod_mul (s : finset A) (f g : A → int) : Prod s (λx, f x * g x) = Prod s f * Prod s g :=
  algebra.finset.Prod_mul s f g
section deceqA
  include deceqA
  theorem Prod_insert_of_mem (f : A → int) {a : A} {s : finset A} (H : a ∈ s) :
    Prod (insert a s) f = Prod s f := algebra.finset.Prod_insert_of_mem f H
  theorem Prod_insert_of_not_mem (f : A → int) {a : A} {s : finset A} (H : a ∉ s) :
    Prod (insert a s) f = f a * Prod s f := algebra.finset.Prod_insert_of_not_mem f H
  theorem Prod_union (f : A → int) {s₁ s₂ : finset A} (disj : s₁ ∩ s₂ = ∅) :
    Prod (s₁ ∪ s₂) f = Prod s₁ f * Prod s₂ f := algebra.finset.Prod_union f disj
  theorem Prod_ext {s : finset A} {f g : A → int} (H : ∀x, x ∈ s → f x = g x) :
    Prod s f = Prod s g := algebra.finset.Prod_ext H
  theorem Prod_one (s : finset A) : Prod s (λ x, 1) = 1 := algebra.finset.Prod_one s
end deceqA

end finset

/- Prod over set -/

namespace set
open set

noncomputable definition Prod (s : set A) (f : A → int) : int := algebra.set.Prod s f
notation `∏` binders `∈` s, r:(scoped f, Prod s f) := r

theorem Prod_empty (f : A → int) : Prod ∅ f = 1 := algebra.set.Prod_empty f
theorem Prod_of_not_finite {s : set A} (nfins : ¬ finite s) (f : A → int) : Prod s f = 1 :=
  algebra.set.Prod_of_not_finite nfins f
theorem Prod_mul (s : set A) (f g : A → int) : Prod s (λx, f x * g x) = Prod s f * Prod s g :=
  algebra.set.Prod_mul s f g
theorem Prod_insert_of_mem (f : A → int) {a : A} {s : set A} (H : a ∈ s) :
  Prod (insert a s) f = Prod s f := algebra.set.Prod_insert_of_mem f H
theorem Prod_insert_of_not_mem (f : A → int) {a : A} {s : set A} [fins : finite s] (H : a ∉ s) :
  Prod (insert a s) f = f a * Prod s f := algebra.set.Prod_insert_of_not_mem f H
theorem Prod_union (f : A → int) {s₁ s₂ : set A} [fins₁ : finite s₁] [fins₂ : finite s₂]
    (disj : s₁ ∩ s₂ = ∅) :
  Prod (s₁ ∪ s₂) f = Prod s₁ f * Prod s₂ f := algebra.set.Prod_union f disj
theorem Prod_ext {s : set A} {f g : A → int} (H : ∀x, x ∈ s → f x = g x) :
  Prod s f = Prod s g := algebra.set.Prod_ext H
theorem Prod_one (s : set A) : Prod s (λ x, 1) = 1 := algebra.set.Prod_one s

end set

/- Suml -/

definition Suml (l : list A) (f : A → int) : int := algebra.Suml l f
notation `∑` binders `←` l, r:(scoped f, Suml l f) := r

theorem Suml_nil (f : A → int) : Suml [] f = 0 := algebra.Suml_nil f
theorem Suml_cons (f : A → int) (a : A) (l : list A) : Suml (a::l) f = f a + Suml l f :=
  algebra.Suml_cons f a l
theorem Suml_append (l₁ l₂ : list A) (f : A → int) : Suml (l₁++l₂) f = Suml l₁ f + Suml l₂ f :=
  algebra.Suml_append l₁ l₂ f
theorem Suml_add (l : list A) (f g : A → int) : Suml l (λx, f x + g x) = Suml l f + Suml l g :=
  algebra.Suml_add l f g
section deceqA
  include deceqA
  theorem Suml_insert_of_mem (f : A → int) {a : A} {l : list A} (H : a ∈ l) :
    Suml (insert a l) f = Suml l f := algebra.Suml_insert_of_mem f H
  theorem Suml_insert_of_not_mem (f : A → int) {a : A} {l : list A} (H : a ∉ l) :
    Suml (insert a l) f = f a + Suml l f := algebra.Suml_insert_of_not_mem f H
  theorem Suml_union {l₁ l₂ : list A} (f : A → int) (d : disjoint l₁ l₂) :
    Suml (union l₁ l₂) f = Suml l₁ f + Suml l₂ f := algebra.Suml_union f d
  theorem Suml_zero (l : list A) : Suml l (λ x, 0) = 0 := algebra.Suml_zero l
end deceqA

/- Sum over a finset -/

namespace finset
open finset
definition Sum (s : finset A) (f : A → int) : int := algebra.finset.Sum s f
notation `∑` binders `∈` s, r:(scoped f, Sum s f) := r

theorem Sum_empty (f : A → int) : Sum ∅ f = 0 := algebra.finset.Sum_empty f
theorem Sum_add (s : finset A) (f g : A → int) : Sum s (λx, f x + g x) = Sum s f + Sum s g :=
  algebra.finset.Sum_add s f g
section deceqA
  include deceqA
  theorem Sum_insert_of_mem (f : A → int) {a : A} {s : finset A} (H : a ∈ s) :
    Sum (insert a s) f = Sum s f := algebra.finset.Sum_insert_of_mem f H
  theorem Sum_insert_of_not_mem (f : A → int) {a : A} {s : finset A} (H : a ∉ s) :
    Sum (insert a s) f = f a + Sum s f := algebra.finset.Sum_insert_of_not_mem f H
  theorem Sum_union (f : A → int) {s₁ s₂ : finset A} (disj : s₁ ∩ s₂ = ∅) :
    Sum (s₁ ∪ s₂) f = Sum s₁ f + Sum s₂ f := algebra.finset.Sum_union f disj
  theorem Sum_ext {s : finset A} {f g : A → int} (H : ∀x, x ∈ s → f x = g x) :
    Sum s f = Sum s g := algebra.finset.Sum_ext H
  theorem Sum_zero (s : finset A) : Sum s (λ x, 0) = 0 := algebra.finset.Sum_zero s
end deceqA

end finset

/- Sum over a set -/

namespace set
open set

noncomputable definition Sum (s : set A) (f : A → int) : int := algebra.set.Sum s f
notation `∏` binders `∈` s, r:(scoped f, Sum s f) := r

theorem Sum_empty (f : A → int) : Sum ∅ f = 0 := algebra.set.Sum_empty f
theorem Sum_of_not_finite {s : set A} (nfins : ¬ finite s) (f : A → int) : Sum s f = 0 :=
  algebra.set.Sum_of_not_finite nfins f
theorem Sum_add (s : set A) (f g : A → int) : Sum s (λx, f x + g x) = Sum s f + Sum s g :=
  algebra.set.Sum_add s f g
theorem Sum_insert_of_mem (f : A → int) {a : A} {s : set A} (H : a ∈ s) :
  Sum (insert a s) f = Sum s f := algebra.set.Sum_insert_of_mem f H
theorem Sum_insert_of_not_mem (f : A → int) {a : A} {s : set A} [fins : finite s] (H : a ∉ s) :
  Sum (insert a s) f = f a + Sum s f := algebra.set.Sum_insert_of_not_mem f H
theorem Sum_union (f : A → int) {s₁ s₂ : set A} [fins₁ : finite s₁] [fins₂ : finite s₂]
    (disj : s₁ ∩ s₂ = ∅) :
  Sum (s₁ ∪ s₂) f = Sum s₁ f + Sum s₂ f := algebra.set.Sum_union f disj
theorem Sum_ext {s : set A} {f g : A → int} (H : ∀x, x ∈ s → f x = g x) :
  Sum s f = Sum s g := algebra.set.Sum_ext H
theorem Sum_zero (s : set A) : Sum s (λ x, 0) = 0 := algebra.set.Sum_zero s

end set

end int
