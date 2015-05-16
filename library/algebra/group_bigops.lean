/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

Finite products on a monoid, and finite sums on an additive monoid. These are called

  algebra.list.prod
  algebra.finset.prod
  algebra.list.sum
  algebra.finset.sum

So when we open algebra we have list.prod etc., and when we migrate to nat, we have
nat.list.prod etc.

We have to be careful with dependencies. This theory imports files from finset and list, which
import basic files from nat. Then nat imports this file to instantiate finite products and sums.
-/
import .group data.list.basic data.list.perm data.finset.basic
open algebra function binary quot subtype

namespace algebra

/- list.prod -/

namespace list -- i.e. algebra.list
  open list    -- i.e. ordinary lists

  variable {A : Type}

  section monoid
  variables {B : Type} [mB : monoid B]
  include mB

  definition mulf (f : A → B) : B → A → B :=
  λ b a, b * f a

  definition prod (l : list A) (f : A → B) : B :=
  list.foldl (mulf f) 1 l

  -- ∏ x ← l, f x
  notation `∏` binders `←` l, r:(scoped f, prod l f) := r

  private theorem foldl_const (f : A → B) :
    ∀ (l : list A) (b : B), foldl (mulf f) b l = b * foldl (mulf f) 1 l
  | []     b := by rewrite [*foldl_nil, mul_one]
  | (a::l) b := by rewrite [*foldl_cons, foldl_const, {foldl _ (mulf f 1 a) _}foldl_const, ↑mulf,
                             one_mul, mul.assoc]

  theorem prod_nil (f : A → B) : prod [] f = 1 := rfl

  theorem prod_cons (f : A → B) (a : A) (l : list A) : prod (a::l) f = f a * prod l f :=
  by rewrite [↑prod, foldl_cons, foldl_const, ↑mulf, one_mul]

  theorem prod_append :
    ∀ (l₁ l₂ : list A) (f : A → B), prod (l₁++l₂) f = prod l₁ f * prod l₂ f
  | []    l₂ f  := by rewrite [append_nil_left, prod_nil, one_mul]
  | (a::l) l₂ f := by rewrite [append_cons, *prod_cons, prod_append, mul.assoc]

  section decidable_eq
  variable [H : decidable_eq A]
  include H

  theorem prod_insert_of_mem (f : A → B) {a : A} {l : list A} : a ∈ l →
    prod (insert a l) f = prod l f :=
  assume ainl, by rewrite [insert_eq_of_mem ainl]

  theorem prod_insert_of_not_mem (f : A → B) {a : A} {l : list A} :
    a ∉ l → prod (insert a l) f = f a * prod l f :=
  assume nainl, by rewrite [insert_eq_of_not_mem nainl, prod_cons]

  theorem prod_union {l₁ l₂ : list A} (f : A → B) (d : disjoint l₁ l₂) :
    prod (union l₁ l₂) f = prod l₁ f * prod l₂ f :=
  by rewrite [union_eq_append d, prod_append]

  end decidable_eq
  end monoid

  section comm_monoid
  variables {B : Type} [cmB : comm_monoid B]
  include cmB

  theorem prod_mul (l : list A) (f g : A → B) : prod l (λx, f x * g x) = prod l f * prod l g :=
  list.induction_on l
     (by rewrite [*prod_nil, mul_one])
     (take a l,
       assume IH,
       by rewrite [*prod_cons, IH, *mul.assoc, mul.left_comm (prod l f)])

  end comm_monoid
end list

/- finset.prod -/

namespace finset
  open finset
  variables {A B : Type}
  variable [cmB : comm_monoid B]
  include cmB

  theorem mulf_rcomm (f : A → B) : right_commutative (list.mulf f) :=
  right_commutative_compose_right (@has_mul.mul B cmB) f (@mul.right_comm B cmB)

  section
  open perm
  theorem listprod_of_perm (f : A → B) {l₁ l₂ : list A} :
    l₁ ~ l₂ → list.prod l₁ f = list.prod l₂ f :=
  λ p, foldl_eq_of_perm (mulf_rcomm f) p 1
  end

  definition prod (s : finset A) (f : A → B) : B :=
  quot.lift_on s
  (λ l, list.prod (elt_of l) f)
  (λ l₁ l₂ p, listprod_of_perm f p)

  -- ∏ x ∈ s, f x
  notation `∏` binders `∈` s, r:(scoped f, prod s f) := r

  theorem prod_empty (f : A → B) : prod ∅ f = 1 :=
  list.prod_nil f

  section decidable_eq
  variable [H : decidable_eq A]
  include H

  theorem prod_insert_of_mem (f : A → B) {a : A} {s : finset A} :
    a ∈ s → prod (insert a s) f = prod s f :=
  quot.induction_on s
    (λ l ainl, list.prod_insert_of_mem f ainl)

  theorem prod_insert_of_not_mem (f : A → B) {a : A} {s : finset A} :
    a ∉ s → prod (insert a s) f = f a * prod s f :=
  quot.induction_on s
    (λ l nainl, list.prod_insert_of_not_mem f nainl)

  theorem prod_union (f : A → B) {s₁ s₂ : finset A} (disj : s₁ ∩ s₂ = ∅) :
    prod (s₁ ∪ s₂) f = prod s₁ f * prod s₂ f :=
  have H1 : disjoint s₁ s₂ → prod (s₁ ∪ s₂) f = prod s₁ f * prod s₂ f, from
    quot.induction_on₂ s₁ s₂
      (λ l₁ l₂ d, list.prod_union f d),
  H1 (disjoint_of_inter_empty disj)

  theorem prod_mul (s : finset A) (f g : A → B) : prod s (λx, f x * g x) = prod s f * prod s g :=
  quot.induction_on s (take u, !list.prod_mul)

  end decidable_eq
end finset

/- list.sum -/

namespace list
  open list
  variable {A : Type}

  section add_monoid
  variables {B : Type} [amB : add_monoid B]
  include amB
  local attribute add_monoid.to_monoid [instance]

  definition sum (l : list A) (f : A → B) : B := prod l f

  -- ∑ x ← l, f x
  notation `∑` binders `←` l, r:(scoped f, sum l f) := r

  theorem sum_nil (f : A → B) : sum [] f = 0 := prod_nil f
  theorem sum_cons (f : A → B) (a : A) (l : list A) : sum (a::l) f = f a + sum l f :=
    prod_cons f a l
  theorem sum_append (l₁ l₂ : list A) (f : A → B) : sum (l₁++l₂) f = sum l₁ f + sum l₂ f :=
    prod_append l₁ l₂ f

  section decidable_eq
  variable [H : decidable_eq A]
  include H

  theorem sum_insert_of_mem (f : A → B) {a : A} {l : list A} (H : a ∈ l) :
    sum (insert a l) f = sum l f := prod_insert_of_mem f H
  theorem sum_insert_of_not_mem (f : A → B) {a : A} {l : list A} (H : a ∉ l) :
    sum (insert a l) f = f a * sum l f := prod_insert_of_not_mem f H
  theorem sum_union {l₁ l₂ : list A} (f : A → B) (d : disjoint l₁ l₂) :
    sum (union l₁ l₂) f = sum l₁ f + sum l₂ f := prod_union f d
  end decidable_eq
  end add_monoid

  section add_comm_monoid
  variables {B : Type} [acmB : add_comm_monoid B]
  include acmB
  local attribute add_comm_monoid.to_comm_monoid [instance]

  theorem sum_add (l : list A) (f g : A → B) : sum l (λx, f x + g x) = sum l f + sum l g :=
    prod_mul l f g
  end add_comm_monoid
end list

/- finset.sum -/

namespace finset
  open finset
  variable {A : Type}

  section add_comm_monoid
  variables {B : Type} [acmB : add_comm_monoid B]
  include acmB
  local attribute add_comm_monoid.to_comm_monoid [instance]

  definition sum (s : finset A) (f : A → B) : B := prod s f

  -- ∑ x ∈ s, f x
  notation `∑` binders `∈` s, r:(scoped f, sum s f) := r

  theorem sum_empty (f : A → B) : sum ∅ f = 0 := prod_empty f

  section decidable_eq
  variable [H : decidable_eq A]
  include H

  theorem sum_insert_of_mem (f : A → B) {a : A} {s : finset A} (H : a ∈ s) :
    sum (insert a s) f = sum s f := prod_insert_of_mem f H
  theorem sum_insert_of_not_mem (f : A → B) {a : A} {s : finset A} (H : a ∉ s) :
    sum (insert a s) f = f a + sum s f := prod_insert_of_not_mem f H
  theorem sum_union (f : A → B) {s₁ s₂ : finset A} (disj : s₁ ∩ s₂ = ∅) :
    sum (s₁ ∪ s₂) f = sum s₁ f + sum s₂ f := prod_union f disj
  theorem sum_add (s : finset A) (f g : A → B) :
    sum s (λx, f x + g x) = sum s f + sum s g := prod_mul s f g

  end decidable_eq
  end add_comm_monoid
end finset

end algebra
