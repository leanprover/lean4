-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

-- The predicative version of inhabited
-- TODO: restore instances

-- import logic bool
-- using logic

namespace predicative

inductive inhabited (A : Type) : Type :=
| inhabited_intro : A → inhabited A

theorem inhabited_elim {A : Type} {B : Type} (H1 : inhabited A) (H2 : A → B) : B
:= inhabited_rec H2 H1

end predicative

-- theorem inhabited_fun [instance] (A : Type) {B : Type} (H : inhabited B) : inhabited (A → B)
-- := inhabited_elim H (take (b : B), inhabited_intro (λ a : A, b))

-- theorem inhabited_sum_left [instance] {A : Type} (B : Type) (H : inhabited A) : inhabited (A + B)
-- := inhabited_elim H (λ a, inhabited_intro (inl B a))

-- theorem inhabited_sum_right [instance] (A : Type) {B : Type} (H : inhabited B) : inhabited (A + B)
-- := inhabited_elim H (λ b, inhabited_intro (inr A b))

-- theorem inhabited_product [instance] {A : Type} {B : Type} (Ha : inhabited A) (Hb : inhabited B) : inhabited (A × B)
-- := inhabited_elim Ha (λ a, (inhabited_elim Hb (λ b, inhabited_intro (a, b))))

-- theorem inhabited_bool [instance] : inhabited bool
-- := inhabited_intro true

-- theorem inhabited_unit [instance] : inhabited unit
-- := inhabited_intro ⋆

-- theorem inhabited_sigma_pr1 {A : Type} {B : A → Type} (p : Σ x, B x) : inhabited A
-- := inhabited_intro (dpr1 p)
