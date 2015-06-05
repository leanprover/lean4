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

end partition
end finset
