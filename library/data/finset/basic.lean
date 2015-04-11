/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.finset
Author: Leonardo de Moura

Finite sets
-/
import data.fintype data.nat data.list.perm data.subtype algebra.binary
open nat quot list subtype binary function
open [declarations] perm

definition nodup_list (A : Type) := {l : list A | nodup l}

variable {A : Type}

definition to_nodup_list_of_nodup {l : list A} (n : nodup l) : nodup_list A :=
tag l n

definition to_nodup_list [h : decidable_eq A] (l : list A) : nodup_list A :=
@to_nodup_list_of_nodup A (erase_dup l) (nodup_erase_dup l)

namespace finset

private definition eqv (l₁ l₂ : nodup_list A) :=
perm (elt_of l₁) (elt_of l₂)

local infix ~ := eqv

private definition eqv.refl (l : nodup_list A) : l ~ l :=
!perm.refl

private definition eqv.symm {l₁ l₂ : nodup_list A} : l₁ ~ l₂ → l₂ ~ l₁ :=
assume p, perm.symm p

private definition eqv.trans {l₁ l₂ l₃ : nodup_list A} : l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ :=
assume p₁ p₂, perm.trans p₁ p₂

definition nodup_list_setoid [instance] (A : Type) : setoid (nodup_list A) :=
setoid.mk (@eqv A) (mk_equivalence (@eqv A) (@eqv.refl A) (@eqv.symm A) (@eqv.trans A))

definition finset (A : Type) : Type :=
quot (nodup_list_setoid A)

definition to_finset_of_nodup (l : list A) (n : nodup l) : finset A :=
⟦to_nodup_list_of_nodup n⟧

definition to_finset [h : decidable_eq A] (l : list A) : finset A :=
⟦to_nodup_list l⟧

definition has_decidable_eq [instance] [h : decidable_eq A] : decidable_eq (finset A) :=
λ s₁ s₂, quot.rec_on_subsingleton₂ s₁ s₂
  (λ l₁ l₂,
     match decidable_perm (elt_of l₁) (elt_of l₂) with
     | decidable.inl e := decidable.inl (quot.sound e)
     | decidable.inr n := decidable.inr (λ e : ⟦l₁⟧ = ⟦l₂⟧, absurd (quot.exact e) n)
     end)

definition singleton (a : A) : finset A :=
to_finset_of_nodup [a] !nodup_singleton

definition mem (a : A) (s : finset A) : Prop :=
quot.lift_on s (λ l, a ∈ elt_of l)
 (λ l₁ l₂ (e : l₁ ~ l₂), propext (iff.intro
   (λ ainl₁, mem_perm e ainl₁)
   (λ ainl₂, mem_perm (perm.symm e) ainl₂)))

infix `∈` := mem
notation a ∉ b := ¬ mem a b

theorem mem_of_mem_list {a : A} {l : nodup_list A} : a ∈ elt_of l → a ∈ ⟦l⟧ :=
λ ainl, ainl

theorem mem_list_of_mem {a : A} {l : nodup_list A} : a ∈ ⟦l⟧ → a ∈ elt_of l :=
λ ainl, ainl

theorem mem_singleton (a : A) : a ∈ singleton a :=
mem_of_mem_list !mem_cons

definition decidable_mem [instance] [h : decidable_eq A] : ∀ (a : A) (s : finset A), decidable (a ∈ s) :=
λ a s, quot.rec_on_subsingleton s
  (λ l, match list.decidable_mem a (elt_of l) with
        | decidable.inl p := decidable.inl (mem_of_mem_list p)
        | decidable.inr n := decidable.inr (λ p, absurd (mem_list_of_mem p) n)
        end)

theorem mem_to_finset [h : decidable_eq A] {a : A} {l : list A} : a ∈ l → a ∈ to_finset l :=
λ ainl, mem_erase_dup ainl

theorem mem_to_finset_of_nodub {a : A} {l : list A} (n : nodup l) : a ∈ l → a ∈ to_finset_of_nodup l n :=
λ ainl, ainl

/- extensionality -/
theorem ext {s₁ s₂ : finset A} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ e, quot.sound (perm_ext (has_property l₁) (has_property l₂) e))

/- empty -/
definition empty : finset A :=
to_finset_of_nodup [] nodup_nil

notation `∅` := !empty

theorem not_mem_empty (a : A) : a ∉ ∅ :=
λ aine : a ∈ ∅, aine

/- universe -/
definition univ [h : fintype A] : finset A :=
to_finset_of_nodup (@fintype.elems A h) (@fintype.unique A h)

theorem mem_univ [h : fintype A] (x : A) : x ∈ univ :=
fintype.complete x

/- card -/
definition card (s : finset A) : nat :=
quot.lift_on s
  (λ l, length (elt_of l))
  (λ l₁ l₂ p, length_eq_length_of_perm p)

theorem card_empty : card (@empty A) = 0 :=
rfl

theorem card_singleton (a : A) : card (singleton a) = 1 :=
rfl

/- insert -/
section insert
variable [h : decidable_eq A]
include h

definition insert (a : A) (s : finset A) : finset A :=
quot.lift_on s
  (λ l, to_finset_of_nodup (insert a (elt_of l)) (nodup_insert a (has_property l)))
  (λ (l₁ l₂ : nodup_list A) (p : l₁ ~ l₂), quot.sound (perm_insert a p))

theorem mem_insert (a : A) (s : finset A) : a ∈ insert a s :=
quot.induction_on s
 (λ l : nodup_list A, mem_to_finset_of_nodub _ !list.mem_insert)

theorem mem_insert_of_mem {a : A} {s : finset A} (b : A) : a ∈ s → a ∈ insert b s :=
quot.induction_on s
 (λ (l : nodup_list A) (ainl : a ∈ ⟦l⟧), mem_to_finset_of_nodub _ (list.mem_insert_of_mem _ ainl))

theorem card_insert_of_mem {a : A} {s : finset A} : a ∈ s → card (insert a s) = card s :=
quot.induction_on s
  (λ (l : nodup_list A) (ainl : a ∈ ⟦l⟧), list.length_insert_of_mem ainl)

theorem card_insert_of_not_mem {a : A} {s : finset A} : a ∉ s → card (insert a s) = card s + 1 :=
quot.induction_on s
  (λ (l : nodup_list A) (nainl : a ∉ ⟦l⟧), list.length_insert_of_not_mem nainl)
end insert

/- erase -/
section erase
variable [h : decidable_eq A]
include h

definition erase (a : A) (s : finset A) : finset A :=
quot.lift_on s
  (λ l, to_finset_of_nodup (erase a (elt_of l)) (nodup_erase_of_nodup a (has_property l)))
  (λ (l₁ l₂ : nodup_list A) (p : l₁ ~ l₂), quot.sound (erase_perm_erase_of_perm a p))

theorem mem_erase (a : A) (s : finset A) : a ∉ erase a s :=
quot.induction_on s
  (λ l, list.mem_erase_of_nodup _ (has_property l))

theorem card_erase_of_mem {a : A} {s : finset A} : a ∈ s → card (erase a s) = pred (card s) :=
quot.induction_on s (λ l ainl, list.length_erase_of_mem ainl)

theorem card_erase_of_not_mem {a : A} {s : finset A} : a ∉ s → card (erase a s) = card s :=
quot.induction_on s (λ l nainl, list.length_erase_of_not_mem nainl)
end erase

/- disjoint -/
definition disjoint (s₁ s₂ : finset A) : Prop :=
quot.lift_on₂ s₁ s₂ (λ l₁ l₂, disjoint (elt_of l₁) (elt_of l₂))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, propext (iff.intro
    (λ d₁ a (ainw₁ : a ∈ elt_of w₁),
      have ainv₁  : a ∈ elt_of v₁, from mem_perm (perm.symm p₁) ainw₁,
      have nainv₂ : a ∉ elt_of v₂, from disjoint_left d₁ ainv₁,
      not_mem_perm p₂ nainv₂)
    (λ d₂ a (ainv₁ : a ∈ elt_of v₁),
      have ainw₁  : a ∈ elt_of w₁, from mem_perm p₁ ainv₁,
      have nainw₂ : a ∉ elt_of w₂, from disjoint_left d₂ ainw₁,
      not_mem_perm (perm.symm p₂) nainw₂)))

theorem disjoint.comm {s₁ s₂ : finset A} : disjoint s₁ s₂ → disjoint s₂ s₁ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ d, list.disjoint.comm d)

/- union -/
section union
variable [h : decidable_eq A]
include h

definition union (s₁ s₂ : finset A) : finset A :=
quot.lift_on₂ s₁ s₂
  (λ l₁ l₂,
    to_finset_of_nodup (list.union (elt_of l₁) (elt_of l₂))
                       (nodup_union_of_nodup_of_nodup (has_property l₁) (has_property l₂)))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound (perm_union p₁ p₂))

notation s₁ ∪ s₂ := union s₁ s₂

theorem mem_union_left {a : A} {s₁ : finset A} (s₂ : finset A) : a ∈ s₁ → a ∈ s₁ ∪ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₁, list.mem_union_left _ ainl₁)

theorem mem_union_right {a : A} {s₂ : finset A} (s₁ : finset A) : a ∈ s₂ → a ∈ s₁ ∪ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₂, list.mem_union_right _ ainl₂)

theorem mem_or_mem_of_mem_union {a : A} {s₁ s₂ : finset A} : a ∈ s₁ ∪ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₁l₂, list.mem_or_mem_of_mem_union ainl₁l₂)

theorem mem_union_eq (a : A) (s₁ s₂ : finset A) : (a ∈ s₁ ∪ s₂) = (a ∈ s₁ ∨ a ∈ s₂) :=
propext (iff.intro
 (λ h, mem_or_mem_of_mem_union h)
 (λ d, or.elim d
   (λ i, mem_union_left _ i)
   (λ i, mem_union_right _ i)))

theorem union.comm (s₁ s₂ : finset A) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
ext (λ a, by rewrite [*mem_union_eq]; exact or.comm)

theorem union.assoc (s₁ s₂ s₃ : finset A) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
ext (λ a, by rewrite [*mem_union_eq]; exact or.assoc)

theorem union_self (s : finset A) : s ∪ s = s :=
ext (λ a, iff.intro
  (λ ain, or.elim (mem_or_mem_of_mem_union ain) (λ i, i) (λ i, i))
  (λ i, mem_union_left _ i))

theorem union_empty (s : finset A) : s ∪ ∅ = s :=
ext (λ a, iff.intro
  (λ ain : a ∈ s ∪ ∅, or.elim (mem_or_mem_of_mem_union ain) (λ i, i) (λ i, absurd i !not_mem_empty))
  (λ i   : a ∈ s, mem_union_left _ i))

theorem empty_union (s : finset A) : ∅ ∪ s = s :=
calc ∅ ∪ s = s ∪ ∅ : union.comm
       ... = s     : union_empty
end union

/- intersection -/
section intersection
variable [h : decidable_eq A]
include h

definition intersection (s₁ s₂ : finset A) : finset A :=
quot.lift_on₂ s₁ s₂
  (λ l₁ l₂,
    to_finset_of_nodup (list.intersection (elt_of l₁) (elt_of l₂))
                       (nodup_intersection_of_nodup _ (has_property l₁)))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound (perm_intersection p₁ p₂))

notation s₁ ∩ s₂ := intersection s₁ s₂

theorem mem_of_mem_intersection_left {a : A} {s₁ s₂ : finset A} : a ∈ s₁ ∩ s₂ → a ∈ s₁ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₁l₂, list.mem_of_mem_intersection_left ainl₁l₂)

theorem mem_of_mem_intersection_right {a : A} {s₁ s₂ : finset A} : a ∈ s₁ ∩ s₂ → a ∈ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₁l₂, list.mem_of_mem_intersection_right ainl₁l₂)

theorem mem_intersection_of_mem_of_mem {a : A} {s₁ s₂ : finset A} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ ainl₁ ainl₂, list.mem_intersection_of_mem_of_mem ainl₁ ainl₂)

theorem mem_intersection_eq (a : A) (s₁ s₂ : finset A) : (a ∈ s₁ ∩ s₂) = (a ∈ s₁ ∧ a ∈ s₂) :=
propext (iff.intro
 (λ h, and.intro (mem_of_mem_intersection_left h) (mem_of_mem_intersection_right h))
 (λ h, mem_intersection_of_mem_of_mem (and.elim_left h) (and.elim_right h)))

theorem intersection.comm (s₁ s₂ : finset A) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
ext (λ a, by rewrite [*mem_intersection_eq]; exact and.comm)

theorem intersection.assoc (s₁ s₂ s₃ : finset A) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
ext (λ a, by rewrite [*mem_intersection_eq]; exact and.assoc)

theorem intersection_self (s : finset A) : s ∩ s = s :=
ext (λ a, iff.intro
  (λ h, mem_of_mem_intersection_right h)
  (λ h, mem_intersection_of_mem_of_mem h h))

theorem intersection_empty (s : finset A) : s ∩ ∅ = ∅ :=
ext (λ a, iff.intro
  (λ h : a ∈ s ∩ ∅, absurd (mem_of_mem_intersection_right h) !not_mem_empty)
  (λ h : a ∈ ∅,     absurd h !not_mem_empty))

theorem empty_intersection (s : finset A) : ∅ ∩ s = ∅ :=
calc ∅ ∩ s = s ∩ ∅ : intersection.comm
       ... = ∅     : intersection_empty
end intersection

/- subset -/
definition subset (s₁ s₂ : finset A) : Prop :=
quot.lift_on₂ s₁ s₂
  (λ l₁ l₂, sublist (elt_of l₁) (elt_of l₂))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, propext (iff.intro
    (λ s₁ a i, mem_perm p₂ (s₁ a (mem_perm (perm.symm p₁) i)))
    (λ s₂ a i, mem_perm (perm.symm p₂) (s₂ a (mem_perm p₁ i)))))

infix `⊆`:50 := subset

theorem nil_sub (s : finset A) : ∅ ⊆ s :=
quot.induction_on s (λ l, list.nil_sub (elt_of l))

theorem sub_univ [h : fintype A] (s : finset A) : s ⊆ univ :=
quot.induction_on s (λ l a i, fintype.complete a)

theorem sub.refl (s : finset A) : s ⊆ s :=
quot.induction_on s (λ l, list.sub.refl (elt_of l))

theorem sub.trans {s₁ s₂ s₃ : finset A} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
quot.induction_on₃ s₁ s₂ s₃ (λ l₁ l₂ l₃ h₁ h₂, list.sub.trans h₁ h₂)

theorem mem_of_sub_of_mem {s₁ s₂ : finset A} {a : A} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
quot.induction_on₂ s₁ s₂ (λ l₁ l₂ h₁ h₂, h₁ a h₂)

/- upto -/
section upto
definition upto (n : nat) : finset nat :=
to_finset_of_nodup (list.upto n) (nodup_upto n)

theorem card_upto : ∀ n, card (upto n) = n :=
list.length_upto

theorem lt_of_mem_upto {n a : nat} : a ∈ upto n → a < n :=
list.lt_of_mem_upto

theorem mem_upto_succ_of_mem_upto {n a : nat} : a ∈ upto n → a ∈ upto (succ n) :=
list.mem_upto_succ_of_mem_upto

theorem mem_upto_of_lt {n a : nat} : a < n → a ∈ upto n :=
list.mem_upto_of_lt
end upto
end finset
