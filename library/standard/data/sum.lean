-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad

import logic.connectives.prop logic.classes.inhabited logic.classes.decidable

using inhabited decidable

namespace sum

-- TODO: take this outside the namespace when the inductive package handles it better
inductive sum (A B : Type) : Type :=
| inl : A → sum A B
| inr : B → sum A B

infixr `+`:25 := sum

theorem cases_on {A B : Type} {C : Prop} (s : A + B) (H1 : A → C) (H2 : B → C) : C :=
sum_rec H1 H2 s

-- TODO: need equality lemmas
-- theorem inl_eq {A : Type} (B : Type) {a1 a2 : A} (H : inl B a1 = inl B a2) : a1 = a2 := sorry

theorem sum_inhabited_left [instance] {A B : Type} (H : inhabited A) : inhabited (A + B) :=
inhabited_mk (inl B (default A))

theorem sum_inhabited_right [instance] {A B : Type} (H : inhabited B) : inhabited (A + B) :=
inhabited_mk (inr A (default B))

--theorem sum_eq_decidable [instance] {A B : Type} (s1 s2 : A + B) : decidable (s1 = s2) :=
--cases_

end sum