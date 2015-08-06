/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about embeddings and surjections
-/

import hit.trunc types.equiv

open equiv sigma sigma.ops eq trunc is_trunc pi is_equiv fiber prod

variables {A B : Type} {f : A → B} {b : B}

structure is_embedding [class] (f : A → B) :=
(elim : Π(a a' : A), is_equiv (ap f : a = a' → f a = f a'))

structure is_surjective [class] (f : A → B) :=
(elim : Π(b : B), ∥ fiber f b ∥)

structure is_split_surjective [class] (f : A → B) :=
(elim : Π(b : B), fiber f b)

structure is_retraction [class] (f : A → B) :=
  (sect : B → A)
  (right_inverse : Π(b : B), f (sect b) = b)

namespace function

  attribute is_embedding.elim [instance]

  definition is_surjective_rec_on {P : Type} (H : is_surjective f) (b : B) [Pt : is_hprop P]
    (IH : fiber f b → P) : P :=
  trunc.rec_on (is_surjective.elim f b) IH

  definition is_surjective_of_is_split_surjective [instance] [H : is_split_surjective f]
    : is_surjective f :=
  is_surjective.mk (λb, tr (is_split_surjective.elim f b))

  definition is_injective_of_is_embedding [reducible] [H : is_embedding f] {a a' : A}
    : f a = f a' → a = a' :=
  (ap f)⁻¹

  definition is_embedding_of_is_injective [HA : is_hset A] [HB : is_hset B]
    (H : Π(a a' : A), f a = f a' → a = a') : is_embedding f :=
  begin
  fapply is_embedding.mk,
  intro a a',
  fapply adjointify,
    {exact (H a a')},
    {intro p, apply is_hset.elim},
    {intro p, apply is_hset.elim}
  end

  definition is_hprop_is_embedding [instance] (f : A → B) : is_hprop (is_embedding f) :=
  begin
    have H : (Π(a a' : A), is_equiv (@ap A B f a a')) ≃ is_embedding f,
    begin
      fapply equiv.MK,
        {exact is_embedding.mk},
        {intro h, cases h, exact elim},
        {intro h, cases h, apply idp},
        {intro p, apply idp},
    end,
    apply is_trunc_equiv_closed,
    exact H,
  end

  definition is_hprop_is_surjective [instance] (f : A → B) : is_hprop (is_surjective f) :=
  begin
    have H : (Π(b : B), merely (fiber f b)) ≃ is_surjective f,
    begin
      fapply equiv.MK,
        {exact is_surjective.mk},
        {intro h, cases h, exact elim},
        {intro h, cases h, apply idp},
        {intro p, apply idp},
    end,
    apply is_trunc_equiv_closed,
    exact H,
  end

  definition is_embedding_of_is_equiv [instance] (f : A → B) [H : is_equiv f] : is_embedding f :=
  is_embedding.mk _

  definition is_equiv_of_is_surjective_of_is_embedding (f : A → B)
    [H : is_embedding f] [H' : is_surjective f] : is_equiv f :=
  @is_equiv_of_is_contr_fun _ _ _
    (λb, is_surjective_rec_on H' b
      (λa, is_contr.mk a
        (λa',
          fiber_eq ((ap f)⁻¹ ((point_eq a) ⬝ (point_eq a')⁻¹))
                   (by rewrite (right_inv (ap f)); rewrite inv_con_cancel_right))))

end function
