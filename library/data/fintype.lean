/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura

Finite type (type class)
-/
import data.list data.bool
open list bool unit decidable

structure fintype [class] (A : Type) : Type :=
(elems : list A) (unique : nodup elems) (complete : ∀ a, a ∈ elems)

definition fintype_unit [instance] : fintype unit :=
fintype.mk [star] dec_trivial (λ u, match u with star := dec_trivial end)

definition fintype_bool [instance] : fintype bool :=
fintype.mk [ff, tt]
  dec_trivial
  (λ b, match b with | tt := dec_trivial | ff := dec_trivial end)

definition fintype_product [instance] {A B : Type} : fintype A → fintype B → fintype (A × B)
| (fintype.mk e₁ u₁ c₁) (fintype.mk e₂ u₂ c₂) :=
  fintype.mk
    (cross_product e₁ e₂)
    (nodup_cross_product u₁ u₂)
    (λ p,
      match p with
      (a, b) := mem_cross_product (c₁ a) (c₂ b)
      end)
