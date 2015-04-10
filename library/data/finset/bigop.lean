/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.finset
Author: Leonardo de Moura

Big operator for finite sets
-/
import algebra.group data.finset.basic data.list.bigop
open algebra finset function binary quot subtype

namespace finset
variables {A B : Type}
variable  [g : comm_group B]
include g

definition bigop (s : finset A) (f : A → B) : B :=
quot.lift_on s
  (λ l, list.bigop (elt_of l) f)
  (λ l₁ l₂ p, list.bigop_of_perm f p)

theorem bigop_empty (f : A → B) : bigop ∅ f = 1 :=
list.bigop_nil f

variable [H : decidable_eq A]
include H

theorem bigop_insert_of_mem (f : A → B) {a : A} {s : finset A} : a ∈ s → bigop (insert a s) f = bigop s f :=
quot.induction_on s
  (λ l ainl, list.bigop_insert_of_mem f ainl)

theorem bigop_insert_of_not_mem (f : A → B) {a : A} {s : finset A} : a ∉ s → bigop (insert a s) f = f a * bigop s f :=
quot.induction_on s
  (λ l nainl, list.bigop_insert_of_not_mem f nainl)

theorem bigop_union (f : A → B) {s₁ s₂ : finset A} : disjoint s₁ s₂ → bigop (s₁ ∪ s₂) f = bigop s₁ f * bigop s₂ f :=
quot.induction_on₂ s₁ s₂
  (λ l₁ l₂ d, list.bigop_union f d)
end finset
