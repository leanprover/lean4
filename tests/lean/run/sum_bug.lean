-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad
import logic
open inhabited decidable
namespace play
-- TODO: take this outside the namespace when the inductive package handles it better
inductive sum (A B : Type) : Type :=
| inl : A → sum A B
| inr : B → sum A B

namespace sum
reserve infixr `+`:25
infixr `+` := sum

open eq

theorem inl_inj {A B : Type} {a1 a2 : A} (H : inl B a1 = inl B a2) : a1 = a2 :=
let f := λs, sum.rec_on s (λa, a1 = a) (λb, false) in
have H1 : f (inl B a1), from rfl,
have H2 : f (inl B a2), from subst H H1,
H2

theorem inl_neq_inr {A B : Type} {a : A} {b : B} (H : inl B a = inr A b) : false :=
let f := λs, sum.rec_on s (λa', a = a') (λb, false) in
have H1 : f (inl B a), from rfl,
have H2 : f (inr A b), from subst H H1,
H2

theorem inr_inj {A B : Type} {b1 b2 : B} (H : inr A b1 = inr A b2) : b1 = b2 :=
let f := λs, sum.rec_on s (λa, false) (λb, b1 = b) in
have H1 : f (inr A b1), from rfl,
have H2 : f (inr A b2), from subst H H1,
H2

theorem sum_inhabited_left [instance] {A B : Type} (H : inhabited A) : inhabited (A + B) :=
inhabited.mk (inl B (default A))

theorem sum_inhabited_right [instance] {A B : Type} (H : inhabited B) : inhabited (A + B) :=
inhabited.mk (inr A (default B))

theorem sum_eq_decidable [instance] {A B : Type} (s1 s2 : A + B)
  (H1 : ∀a1 a2 : A, decidable (inl B a1 = inl B a2))
  (H2 : ∀b1 b2 : B, decidable (inr A b1 = inr A b2)) : decidable (s1 = s2) :=
sum.rec_on s1
  (take a1, show decidable (inl B a1 = s2), from
    sum.rec_on s2
      (take a2, show decidable (inl B a1 = inl B a2), from H1 a1 a2)
      (take b2,
        have H3 : (inl B a1 = inr A b2) ↔ false,
          from iff.intro inl_neq_inr (assume H4, false.elim H4),
        show decidable (inl B a1 = inr A b2), from decidable_of_decidable_of_iff _ (iff.symm H3)))
  (take b1, show decidable (inr A b1 = s2), from
    sum.rec_on s2
      (take a2,
        have H3 : (inr A b1 = inl B a2) ↔ false,
          from iff.intro (assume H4, inl_neq_inr (symm H4)) (assume H4, false.elim H4),
        show decidable (inr A b1 = inl B a2), from decidable_of_decidable_of_iff _ (iff.symm H3))
      (take b2, show decidable (inr A b1 = inr A b2), from H2 b1 b2))

end sum
end play
