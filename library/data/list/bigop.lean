/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.list.bigop
Authors: Leonardo de Moura

Big operator for lists
-/
import algebra.group data.list.comb data.list.set data.list.perm
open algebra function binary quot

namespace list
variables {A B : Type}
variable  [g : monoid B]
include g

definition mulf (f : A → B) : B → A → B :=
λ b a, b * f a

definition bigop (l : list A) (f : A → B) : B :=
foldl (mulf f) 1 l

private theorem foldl_const (f : A → B) : ∀ (l : list A) (b : B), foldl (mulf f) b l = b * foldl (mulf f) 1 l
| []     b := by rewrite [*foldl_nil, mul_one]
| (a::l) b := by rewrite [*foldl_cons, foldl_const, {foldl _ (mulf f 1 a) _}foldl_const, ↑mulf, one_mul, mul.assoc]

theorem bigop_nil (f : A → B) : bigop [] f = 1 :=
rfl

theorem bigop_cons (f : A → B) (a : A) (l : list A) : bigop (a::l) f = f a * bigop l f :=
by rewrite [↑bigop, foldl_cons, foldl_const, ↑mulf, one_mul]

theorem bigop_append : ∀ (l₁ l₂ : list A) (f : A → B), bigop (l₁++l₂) f = bigop l₁ f * bigop l₂ f
| []    l₂ f  := by rewrite [append_nil_left, bigop_nil, one_mul]
| (a::l) l₂ f := by rewrite [append_cons, *bigop_cons, bigop_append, mul.assoc]

section insert
variable [H : decidable_eq A]
include H

theorem bigop_insert_of_mem (f : A → B) {a : A} {l : list A} : a ∈ l → bigop (insert a l) f = bigop l f :=
assume ainl, by rewrite [insert_eq_of_mem ainl]

theorem bigop_insert_of_not_mem (f : A → B) {a : A} {l : list A} : a ∉ l → bigop (insert a l) f = f a * bigop l f :=
assume nainl, by rewrite [insert_eq_of_not_mem nainl, bigop_cons]
end insert

section union
variable [H : decidable_eq A]
include H

definition bigop_union {l₁ l₂ : list A} (f : A → B) (d : disjoint l₁ l₂) : bigop (union l₁ l₂) f = bigop l₁ f * bigop l₂ f :=
by rewrite [union_eq_append d, bigop_append]
end union
end list

namespace list
open perm
variables {A B : Type}
variable  [g : comm_monoid B]
include g

theorem mulf_rcomm (f : A → B) : right_commutative (mulf f) :=
right_commutative_compose_right (@has_mul.mul B g) f (@mul.right_comm B g)

theorem bigop_of_perm (f : A → B) {l₁ l₂ : list A} : l₁ ~ l₂ → bigop l₁ f = bigop l₂ f :=
λ p, foldl_eq_of_perm (mulf_rcomm f) p 1
end list
