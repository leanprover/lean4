/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Haitao Zhang

Partitions of a type A into finite subsets of A. Such a partition is represented by
a function f : A → finset A which maps every element a : A to its equivalence class.
-/
import .card
open function eq.ops

variable {A : Type}
variable [deceqA : decidable_eq A]
include deceqA

namespace finset

definition is_partition (f : A → finset A) := ∀ a b, a ∈ f b = (f a = f b)

structure partition : Type :=
(set : finset A) (part : A → finset A) (is_part : is_partition part)
  (complete : set = Union set part)

attribute partition.part [coercion]

namespace partition

definition equiv_classes (f : partition) : finset (finset A) :=
image (partition.part f) (partition.set f)

lemma equiv_class_disjoint (f : partition) (a1 a2 : finset A) (Pa1 : a1 ∈ equiv_classes f)
    (Pa2 : a2 ∈ equiv_classes f) :
  a1 ≠ a2 → a1 ∩ a2 = ∅ :=
assume Pne,
assert Pe1 : _, from exists_of_mem_image Pa1, obtain g1 Pg1, from Pe1,
assert Pe2 : _, from exists_of_mem_image Pa2, obtain g2 Pg2, from Pe2,
begin
  apply inter_eq_empty_of_disjoint,
  apply disjoint.intro,
  rewrite [eq.symm (and.right Pg1), eq.symm (and.right Pg2)],
  intro x,
  rewrite [*partition.is_part f],
  intro Pxg1, rewrite [Pxg1, and.right Pg1, and.right Pg2],
  intro Pe, exact absurd Pe Pne
end

theorem class_equation (f : @partition A _) :
  card (partition.set f) = nat.Sum (equiv_classes f) card :=
let s := (partition.set f), p := (partition.part f), img := image p s in
  calc
    card s = card (Union s p) : partition.complete f
       ... = card (Union img id) : image_eq_Union_index_image s p
       ... = card (Union (equiv_classes f) id) : rfl
       ... = nat.Sum (equiv_classes f) card : card_Union_of_disjoint _ id (equiv_class_disjoint f)

lemma equiv_class_refl {f : A → finset A} (Pequiv : is_partition f) : ∀ a, a ∈ f a :=
take a, by rewrite [Pequiv a a]

-- make it a little easier to prove union from restriction
lemma restriction_imp_union {s : finset A} (f : A → finset A) (Pequiv : is_partition f)
    (Psub : ∀{a}, a ∈ s → f a ⊆ s) :
  s = Union s f :=
ext (take a, iff.intro
  (assume Pains,
    begin
      rewrite [(Union_insert_of_mem f Pains)⁻¹, Union_insert],
      apply mem_union_l, exact equiv_class_refl Pequiv a
    end)
  (assume Painu,
    have Pclass : ∃ x, x ∈ s ∧ a ∈ f x,
      from iff.elim_left (mem_Union_iff s f _) Painu,
    obtain x Px, from Pclass,
    have Pfx : f x ⊆ s, from Psub (and.left Px),
    mem_of_subset_of_mem Pfx (and.right Px)))

lemma binary_union (P : A → Prop) [decP : decidable_pred P] {S : finset A} :
  S = {a ∈ S | P a} ∪ {a ∈ S | ¬(P a)} :=
ext take a, iff.intro
  (suppose a ∈ S, decidable.by_cases
    (suppose P a, mem_union_l (mem_filter_of_mem `a ∈ S` this))
    (suppose ¬ P a, mem_union_r (mem_filter_of_mem `a ∈ S` this)))
  (suppose a ∈ filter P S ∪ {a ∈ S | ¬ P a}, or.elim (mem_or_mem_of_mem_union this)
    (suppose a ∈ filter P S,      mem_of_mem_filter this)
    (suppose a ∈ {a ∈ S | ¬ P a}, mem_of_mem_filter this))

lemma binary_inter_empty {P : A → Prop} [decP : decidable_pred P] {S : finset A} :
  {a ∈ S | P a} ∩ {a ∈ S | ¬(P a)} = ∅ :=
inter_eq_empty (take a, assume Pa nPa, absurd (of_mem_filter Pa) (of_mem_filter nPa))

definition disjoint_sets (S : finset (finset A)) : Prop :=
  ∀ s₁ s₂ (P₁ : s₁ ∈ S) (P₂ : s₂ ∈ S), s₁ ≠ s₂ → s₁ ∩ s₂ = ∅

lemma disjoint_sets_filter_of_disjoint_sets {P : finset A → Prop} [decP : decidable_pred P] {S : finset (finset A)} :
  disjoint_sets S → disjoint_sets {s ∈ S | P s} :=
assume Pds, take s₁ s₂, assume P₁ P₂, Pds s₁ s₂ (mem_of_mem_filter P₁) (mem_of_mem_filter P₂)

lemma binary_inter_empty_Union_disjoint_sets {P : finset A → Prop} [decP : decidable_pred P] {S : finset (finset A)} :
  disjoint_sets S → Union {s ∈ S | P s} id ∩ Union {s ∈ S | ¬P s} id = ∅ :=
assume Pds, inter_eq_empty (take a, assume Pa nPa,
  obtain s Psin Pains, from iff.elim_left !mem_Union_iff Pa,
  obtain t Ptin Paint, from iff.elim_left !mem_Union_iff nPa,
  assert s ≠ t,
    from assume Peq, absurd (Peq ▸ of_mem_filter Psin) (of_mem_filter Ptin),
  Pds s t (mem_of_mem_filter Psin) (mem_of_mem_filter Ptin) `s ≠ t` ▸ mem_inter Pains Paint)

section
variables {B: Type} [deceqB : decidable_eq B]
include deceqB

lemma binary_Union (f : A → finset B) {P : A → Prop} [decP : decidable_pred P] {s : finset A} :
  Union s f = Union {a ∈ s | P a} f ∪ Union {a ∈ s | ¬P a} f :=
begin rewrite [binary_union P at {1}], apply Union_union, exact binary_inter_empty end

end

open nat
section
open algebra

variables {B : Type} [acmB : add_comm_monoid B]
include acmB

lemma Sum_binary_union (f : A → B) (P : A → Prop) [decP : decidable_pred P] {S : finset A} :
  Sum S f = Sum {s ∈ S | P s} f + Sum {s ∈ S | ¬P s} f :=
calc
  Sum S f = Sum ({s ∈ S | P s} ∪ {s ∈ S | ¬(P s)}) f : binary_union
      ... = Sum {s ∈ S | P s} f + Sum {s ∈ S | ¬P s} f : Sum_union f binary_inter_empty

end

lemma card_binary_Union_disjoint_sets (P : finset A → Prop) [decP : decidable_pred P] {S : finset (finset A)} :
  disjoint_sets S → card (Union S id) = Sum {s ∈ S | P s} card + Sum {s ∈ S | ¬P s} card :=
assume Pds, calc
        card (Union S id)
      = card (Union {s ∈ S | P s} id ∪ Union {s ∈ S | ¬P s} id) : binary_Union
  ... = card (Union {s ∈ S | P s} id) + card (Union {s ∈ S | ¬P s} id) : card_union_of_disjoint (binary_inter_empty_Union_disjoint_sets Pds)
  ... = Sum {s ∈ S | P s} card + Sum {s ∈ S | ¬P s} card : by rewrite [*(card_Union_of_disjoint _ id (disjoint_sets_filter_of_disjoint_sets Pds))]

end partition
end finset
