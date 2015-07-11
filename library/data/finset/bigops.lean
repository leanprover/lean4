/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Haitao Zhang

Finite unions and intersections on finsets.

Note: for the moment we only do unions. We need to generalize bigops for intersections.
-/
import data.finset.comb algebra.group_bigops
open list

namespace finset

variables {A B : Type} [deceqA : decidable_eq A] [deceqB : decidable_eq B]

/- Unionl and Union -/

section union

definition to_comm_monoid_Union (B : Type) [deceqB : decidable_eq B] :
  algebra.comm_monoid (finset B) :=
⦃ algebra.comm_monoid,
  mul         := union,
  mul_assoc   := union.assoc,
  one         := empty,
  mul_one     := union_empty,
  one_mul     := empty_union,
  mul_comm    := union.comm
⦄

open [classes] algebra
local attribute finset.to_comm_monoid_Union [instance]

include deceqB

definition Unionl (l : list A) (f : A → finset B) : finset B := algebra.Prodl l f
notation `⋃` binders `←` l, r:(scoped f, Unionl l f) := r
definition Union (s : finset A) (f : A → finset B) : finset B := algebra.Prod s f
notation `⋃` binders `∈` s, r:(scoped f, finset.Union s f) := r

theorem Unionl_nil (f : A → finset B) : Unionl [] f = ∅ := algebra.Prodl_nil f
theorem Unionl_cons (f : A → finset B) (a : A) (l : list A) :
  Unionl (a::l) f = f a ∪ Unionl l f := algebra.Prodl_cons f a l
theorem Unionl_append (l₁ l₂ : list A) (f : A → finset B) :
  Unionl (l₁++l₂) f = Unionl l₁ f ∪ Unionl l₂ f := algebra.Prodl_append l₁ l₂ f
theorem Unionl_mul (l : list A) (f g : A → finset B) :
  Unionl l (λx, f x ∪ g x) = Unionl l f ∪ Unionl l g := algebra.Prodl_mul l f g
section deceqA
  include deceqA
  theorem Unionl_insert_of_mem (f : A → finset B) {a : A} {l : list A} (H : a ∈ l) :
    Unionl (list.insert a l) f = Unionl l f := algebra.Prodl_insert_of_mem f H
  theorem Unionl_insert_of_not_mem (f : A → finset B) {a : A} {l : list A} (H : a ∉ l) :
    Unionl (list.insert a l) f = f a ∪ Unionl l f := algebra.Prodl_insert_of_not_mem f H
  theorem Unionl_union {l₁ l₂ : list A} (f : A → finset B) (d : list.disjoint l₁ l₂) :
    Unionl (list.union l₁ l₂) f = Unionl l₁ f ∪ Unionl l₂ f := algebra.Prodl_union f d
  theorem Unionl_empty (l : list A) : Unionl l (λ x, ∅) = (∅ : finset B) := algebra.Prodl_one l
end deceqA

theorem Union_empty (f : A → finset B) : Union ∅ f = ∅ := algebra.Prod_empty f
theorem Union_mul (s : finset A) (f g : A → finset B) :
  Union s (λx, f x ∪ g x) = Union s f ∪ Union s g := algebra.Prod_mul s f g
section deceqA
  include deceqA
  theorem Union_insert_of_mem (f : A → finset B) {a : A} {s : finset A} (H : a ∈ s) :
    Union (insert a s) f = Union s f := algebra.Prod_insert_of_mem f H
  private theorem Union_insert_of_not_mem (f : A → finset B) {a : A} {s : finset A} (H : a ∉ s) :
    Union (insert a s) f = f a ∪ Union s f := algebra.Prod_insert_of_not_mem f H
  theorem Union_union (f : A → finset B) {s₁ s₂ : finset A} (disj : s₁ ∩ s₂ = ∅) :
    Union (s₁ ∪ s₂) f = Union s₁ f ∪ Union s₂ f := algebra.Prod_union f disj
  theorem Union_ext {s : finset A} {f g : A → finset B} (H : ∀x, x ∈ s → f x = g x) :
    Union s f = Union s g := algebra.Prod_ext H
  theorem Union_empty' (s : finset A) : Union s (λ x, ∅) = (∅ : finset B) := algebra.Prod_one s

  -- this will eventually be an instance of something more general
  theorem inter_Union (s : finset B) (t : finset A) (f : A → finset B) :
      s ∩ (⋃ x ∈ t, f x) = (⋃ x ∈ t, s ∩ f x) :=
  begin
    induction t with s' x H IH,
      rewrite [*Union_empty, inter_empty],
      rewrite [*Union_insert_of_not_mem _ H, inter.distrib_left, IH],
  end

  theorem mem_Union_iff (s : finset A) (f : A → finset B) (b : B) :
    b ∈ (⋃ x ∈ s, f x) ↔ (∃ x, x ∈ s ∧ b ∈ f x ) :=
  begin
    induction s with s' a H IH,
      rewrite [exists_mem_empty_eq],
      rewrite [Union_insert_of_not_mem _ H, mem_union_eq, IH, exists_mem_insert_eq]
  end

  theorem mem_Union_eq (s : finset A) (f : A → finset B) (b : B) :
    b ∈ (⋃ x ∈ s, f x) = (∃ x, x ∈ s ∧ b ∈ f x ) :=
  propext !mem_Union_iff

  theorem Union_insert (f : A → finset B) {a : A} {s : finset A} :
    Union (insert a s) f = f a ∪ Union s f :=
  decidable.by_cases
    (assume Pin : a ∈ s,
      begin
        rewrite [Union_insert_of_mem f Pin],
        apply ext,
        intro x,
        apply iff.intro,
          exact mem_union_r,
          rewrite [mem_union_eq],
          intro Por,
          exact or.elim Por
            (assume Pl, begin
              rewrite mem_Union_eq, exact (exists.intro a (and.intro Pin Pl)) end)
            (assume Pr, Pr)
      end)
    (assume H : a ∉ s, !Union_insert_of_not_mem H)

  lemma image_eq_Union_index_image (s : finset A) (f : A → finset B) :
    Union s f = Union (image f s) function.id :=
      finset.induction_on s
        (by rewrite Union_empty)
        (take s1 a Pa IH, by rewrite [image_insert, *Union_insert, IH])

  lemma Union_const [deceqB : decidable_eq B] {f : A → finset B} {s : finset A} {t : finset B} :
    s ≠ ∅ → (∀ x, x ∈ s → f x = t) → Union s f = t :=
  begin
    induction s with a' s' H IH,
      {intros [H1, H2], exfalso, apply H1 !rfl},
    intros [H1, H2],
    rewrite [Union_insert, H2 _ !mem_insert],
    cases (decidable.em (s' = ∅)) with [seq, sne],
      {rewrite [seq, Union_empty, union_empty]},
    have H3 : ∀ x, x ∈ s' → f x = t, from (λ x H', H2 x (mem_insert_of_mem _ H')),
    rewrite [IH sne H3, union_self]
  end
end deceqA

end union

end finset
