-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Floris van Doorn
-- Ported from Coq HoTT
import .path data.nat.basic data.empty data.unit
open path nat

-- Truncation levels
-- -----------------

-- TODO: make everything universe polymorphic

structure contr_internal (A : Type₊) :=
mk :: (center : A) (contr : Π(a : A), center ≈ a)

inductive trunc_index : Type :=
minus_two : trunc_index,
trunc_S : trunc_index → trunc_index

namespace truncation

postfix `.+1`:max := trunc_index.trunc_S
postfix `.+2`:max := λn, (n .+1 .+1)
notation `-2` := trunc_index.minus_two
notation `-1` := (-2.+1)

definition trunc_index_add (n m : trunc_index) : trunc_index :=
trunc_index.rec_on m n (λ k l, l .+1)

-- Coq calls this `-2+`, but `+2+` looks more natural, since trunc_index_add 0 0 = 2
infix `+2+`:65 := trunc_index_add

definition trunc_index_leq (n m : trunc_index) : Type₁ :=
trunc_index.rec_on n (λm, unit) (λ n p m, trunc_index.rec_on m (λ p, empty) (λ m q p, p m) p) m

notation x <= y := trunc_index_leq x y
notation x ≤ y := trunc_index_leq x y

definition nat_to_trunc_index [coercion] (n : nat) : trunc_index :=
nat.rec_on n (-1.+1) (λ n k, k.+1)

definition is_trunc_internal (n : trunc_index) : Type₁ → Type₁ :=
trunc_index.rec_on n (λA, contr_internal A) (λn trunc_n A, (Π(x y : A), trunc_n (x ≈ y)))

structure is_trunc [class] (n : trunc_index) (A : Type) :=
mk :: (to_internal : is_trunc_internal n A)

--prefix `is_contr`:max := is_trunc -2
definition is_contr := is_trunc -2
definition is_hprop := is_trunc -1
definition is_hset := is_trunc nat.zero

variable {A : Type₁}

definition is_contr.mk (center : A) (contr : Π(a : A), center ≈ a) : is_contr A :=
is_trunc.mk (contr_internal.mk center contr)

definition center (A : Type₁) [H : is_contr A] : A :=
@contr_internal.center A is_trunc.to_internal

definition contr [H : is_contr A] (a : A) : !center ≈ a :=
@contr_internal.contr A is_trunc.to_internal a

definition is_trunc_succ (A : Type₁) {n : trunc_index} [H : ∀x y : A, is_trunc n (x ≈ y)]
  : is_trunc (n.+1) A :=
is_trunc.mk (λ x y, is_trunc.to_internal)

definition succ_is_trunc {n : trunc_index} [H : is_trunc (n.+1) A] (x y : A) : is_trunc n (x ≈ y) :=
is_trunc.mk (is_trunc.to_internal x y)

definition path_contr [H : is_contr A] (x y : A) : x ≈ y :=
(contr x)⁻¹ ⬝ (contr y)

definition path2_contr {A : Type₁} [H : is_contr A] {x y : A} (p q : x ≈ y) : p ≈ q :=
have K : ∀ (r : x ≈ y), path_contr x y ≈ r, from
  (λ r, path.rec_on r !concat_Vp),
K p⁻¹ ⬝ K q

definition contr_paths_contr [instance] {A : Type₁} [H : is_contr A] (x y : A) : is_contr (x ≈ y) :=
is_contr.mk !path_contr (λ p, !path2_contr)

definition trunc_succ (A : Type₁) (n : trunc_index) [H : is_trunc n A] : is_trunc (n.+1) A :=
trunc_index.rec_on n
  (λ A (H : is_contr A), !is_trunc_succ)
  (λ n IH A (H : is_trunc (n.+1) A), @is_trunc_succ _ _ (λ x y, IH _ !succ_is_trunc))
  A H
--in the proof the type of H is given explicitly to make it available for class inference

definition trunc_leq [instance] {A : Type₁} {m n : trunc_index} (H : m ≤ n)
  [H : is_trunc m A] : is_trunc n A :=
sorry

definition is_hprop.mk (A : Type₁) (H : ∀x y : A, x ≈ y) : is_hprop A := sorry
definition is_hprop.elim [H : is_hprop A] (x y : A) : x ≈ y := sorry

definition is_trunc_is_hprop {n : trunc_index} : is_hprop (is_trunc n A) := sorry

definition is_hset.mk (A : Type₁) (H : ∀(x y : A) (p q : x ≈ y), p ≈ q) : is_hset A := sorry
definition is_hset.elim [H : is_hset A] ⦃x y : A⦄ (p q : x ≈ y) : p ≈ q := sorry


end truncation
