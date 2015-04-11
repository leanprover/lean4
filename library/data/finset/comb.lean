/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.finset
Author: Leonardo de Moura

Combinators for finite sets
-/
import data.finset.basic
open list quot subtype decidable perm function

namespace finset
variables {A B : Type}
variable [h : decidable_eq B]
include h

definition map (f : A → B) (s : finset A) : finset B :=
quot.lift_on s
  (λ l, to_finset (list.map f (elt_of l)))
  (λ l₁ l₂ p, quot.sound (perm_erase_dup_of_perm (perm_map _ p)))

theorem map_empty (f : A → B) : map f ∅ = ∅ :=
rfl
end finset
