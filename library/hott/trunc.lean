-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Floris van Doorn
-- Ported from Coq HoTT
import .path data.nat data.empty data.unit
open path nat

-- Truncation levels
-- -----------------

structure contr_internal [class] (A : Type₊) :=
mk :: (center : A) (contr : Π(a : A), center ≈ a)
-- TODO: center and contr should live in different namespaces

inductive trunc_index : Type :=
minus_two : trunc_index,
trunc_S : trunc_index → trunc_index

namespace truncation

postfix `.+1`:max := trunc_index.trunc_S
postfix `.+2`:max := λn, (n .+1 .+1)
notation `-2`:max := trunc_index.minus_two
notation `-1`:max := (-2.+1)

definition trunc_index_add (n m : trunc_index) : trunc_index :=
trunc_index.rec_on m n (λ k l, l .+1)

-- Coq calls this `-2+`, but this looks more natural, since 0 +2+ 0 = 2
infix `+2+`:65 := trunc_index_add

definition trunc_index_leq (n m : trunc_index) : Type₁ :=
trunc_index.rec_on n (λm, unit) (λ n p m, trunc_index.rec_on m (λ p, empty) (λ m q p, p m) p) m

notation `<=` := trunc_index_leq
notation `≤` := trunc_index_leq

definition nat_to_trunc_index [coercion] (n : ℕ) : trunc_index :=
nat.rec_on n (-2.+2) (λ n k, k.+1)

-- TODO: note in the Coq version, there is an internal version
definition is_trunc_internal (n : trunc_index) : Type₁ → Type₁ :=
trunc_index.rec_on n (λA, contr_internal A) (λn trunc_n A, (Π(x y : A), trunc_n (x ≈ y)))

structure is_trunc [class] (n : trunc_index) (A : Type) :=
mk :: (trunc_is_trunc : is_trunc_internal n A)

definition is_contr := is_trunc -2
definition is_hProp := is_trunc -1
definition is_hSet := is_trunc 0

definition contr_to_internal {A : Type₁} [H : is_contr A] : contr_internal A :=
is_trunc.trunc_is_trunc

definition internal_to_contr {A : Type₁} [H : contr_internal A] : is_contr A :=
is_trunc.mk H

definition contr_mk {A : Type₁} (center : A) (contr : Π(a : A), center ≈ a) : is_contr A :=
is_trunc.mk (contr_internal.mk center contr)

definition center {A : Type₁} [H : is_contr A] : A :=
@contr_internal.center A is_trunc.trunc_is_trunc

definition contr {A : Type₁} [H : is_contr A] (a : A) : center ≈ a :=
@contr_internal.contr A is_trunc.trunc_is_trunc a

definition path_contr {A : Type₁} [H : is_contr A] (x y : A) : x ≈ y :=
(contr x)⁻¹ ⬝ (contr y)

definition path2_contr {A : Type₁} [H : is_contr A] {x y : A} (p q : x ≈ y) : p ≈ q :=
have K : ∀ (r : x ≈ y), path_contr x y ≈ r, from
  (λ r, path.rec_on r !concat_Vp),
K p⁻¹ ⬝ K q

definition contr_paths_contr [instance] {A : Type₁} [H : is_contr A] (x y : A) : is_contr (x ≈ y) :=
contr_mk !path_contr (λ p, !path2_contr)

definition trunc_succ [instance] {A : Type₁} (n : trunc_index) [H : is_trunc n A] : is_trunc (n.+1) A :=
trunc_index.rec_on n
  (λ A H, @is_trunc.mk -1 _ (λ x y, @contr_to_internal _ (@contr_paths_contr _ H _ _)))
  (λ n IH A H, is_trunc.mk (λ x y, @is_trunc.trunc_is_trunc (n.+1) (x≈y) (IH _
    (@is_trunc.mk n (x≈y) (@is_trunc.trunc_is_trunc (n.+1) _ H x y))
    )))
  A H

definition trunc_leq [instance] {A : Type₁} {m n : trunc_index} (H : trunc_index_leq m n)
  [H : is_trunc m A] : is_trunc n A :=
sorry

end truncation
