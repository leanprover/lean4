/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about embeddings and surjections
-/

import hit.trunc types.equiv cubical.square

open equiv sigma sigma.ops eq trunc is_trunc pi is_equiv fiber prod

variables {A B : Type} (f : A → B) {b : B}

definition is_embedding [class] (f : A → B) := Π(a a' : A), is_equiv (ap f : a = a' → f a = f a')

definition is_surjective [class] (f : A → B) := Π(b : B), ∥ fiber f b ∥

definition is_split_surjective [class] (f : A → B) := Π(b : B), fiber f b

structure is_retraction [class] (f : A → B) :=
  (sect : B → A)
  (right_inverse : Π(b : B), f (sect b) = b)

structure is_section [class] (f : A → B) :=
  (retr : B → A)
  (left_inverse : Π(a : A), retr (f a) = a)

definition is_weakly_constant [class] (f : A → B) := Π(a a' : A), f a = f a'

structure is_constant [class] (f : A → B) :=
  (pt : B)
  (eq : Π(a : A), f a = pt)

structure is_conditionally_constant [class] (f : A → B) :=
  (g : ∥A∥ → B)
  (eq : Π(a : A), f a = g (tr a))

namespace function

  abbreviation sect          [unfold 4] := @is_retraction.sect
  abbreviation right_inverse [unfold 4] := @is_retraction.right_inverse
  abbreviation retr          [unfold 4] := @is_section.retr
  abbreviation left_inverse  [unfold 4] := @is_section.left_inverse

  definition is_equiv_ap_of_embedding [instance] [H : is_embedding f] (a a' : A)
    : is_equiv (ap f : a = a' → f a = f a') :=
  H a a'

  variable {f}
  definition is_injective_of_is_embedding [reducible] [H : is_embedding f] {a a' : A}
    : f a = f a' → a = a' :=
  (ap f)⁻¹

  definition is_embedding_of_is_injective [HA : is_hset A] [HB : is_hset B]
    (H : Π(a a' : A), f a = f a' → a = a') : is_embedding f :=
  begin
  intro a a',
  fapply adjointify,
    {exact (H a a')},
    {intro p, apply is_hset.elim},
    {intro p, apply is_hset.elim}
  end
  variable (f)

  definition is_hprop_is_embedding [instance] : is_hprop (is_embedding f) :=
  by unfold is_embedding; exact _

  definition is_hprop_fiber_of_is_embedding [H : is_embedding f] (b : B) :
    is_hprop (fiber f b) :=
  begin
    apply is_hprop.mk, intro v w,
    induction v with a p, induction w with a' q, induction q,
    fapply fiber_eq,
    { esimp, apply is_injective_of_is_embedding p},
    { esimp [is_injective_of_is_embedding], symmetry, apply right_inv}
  end

  variable {f}
  definition is_surjective_rec_on {P : Type} (H : is_surjective f) (b : B) [Pt : is_hprop P]
    (IH : fiber f b → P) : P :=
  trunc.rec_on (H b) IH
  variable (f)

  definition is_surjective_of_is_split_surjective [instance] [H : is_split_surjective f]
    : is_surjective f :=
  λb, tr (H b)

  definition is_hprop_is_surjective [instance] : is_hprop (is_surjective f) :=
  by unfold is_surjective; exact _

  definition is_weakly_constant_ap [instance] [H : is_weakly_constant f] (a a' : A) :
    is_weakly_constant (ap f : a = a' → f a = f a') :=
  take p q : a = a',
  have Π{b c : A} {r : b = c}, (H a b)⁻¹ ⬝ H a c = ap f r, from
    (λb c r, eq.rec_on r !con.left_inv),
  this⁻¹ ⬝ this

  definition is_constant_ap [unfold 4] [instance] [H : is_constant f] (a a' : A)
    : is_constant (ap f : a = a' → f a = f a') :=
  begin
    induction H with b q,
    fapply is_constant.mk,
    { exact q a ⬝ (q a')⁻¹},
    { intro p, induction p, exact !con.right_inv⁻¹}
  end

  definition is_contr_is_retraction [instance] [H : is_equiv f] : is_contr (is_retraction f) :=
  begin
    have H2 : (Σ(g : B → A), Πb, f (g b) = b) ≃ is_retraction f,
    begin
      fapply equiv.MK,
        {intro x, induction x with g p, constructor, exact p},
        {intro h, induction h, apply sigma.mk, assumption},
        {intro h, induction h, reflexivity},
        {intro x, induction x, reflexivity},
    end,
    apply is_trunc_equiv_closed, exact H2,
    apply is_equiv.is_contr_right_inverse
  end

  definition is_contr_is_section [instance] [H : is_equiv f] : is_contr (is_section f) :=
  begin
    have H2 : (Σ(g : B → A), Πa, g (f a) = a) ≃ is_section f,
    begin
      fapply equiv.MK,
        {intro x, induction x with g p, constructor, exact p},
        {intro h, induction h, apply sigma.mk, assumption},
        {intro h, induction h, reflexivity},
        {intro x, induction x, reflexivity},
    end,
    apply is_trunc_equiv_closed, exact H2,
    fapply is_trunc_equiv_closed,
      {apply sigma_equiv_sigma_id, intro g, apply eq_equiv_homotopy},
    fapply is_trunc_equiv_closed,
      {apply fiber.sigma_char},
    fapply is_contr_fiber_of_is_equiv,
    exact to_is_equiv (arrow_equiv_arrow_left_rev A (equiv.mk f H)),
  end

  definition is_embedding_of_is_equiv [instance] [H : is_equiv f] : is_embedding f :=
  λa a', _

  definition is_equiv_of_is_surjective_of_is_embedding
    [H : is_embedding f] [H' : is_surjective f] : is_equiv f :=
  @is_equiv_of_is_contr_fun _ _ _
    (λb, is_surjective_rec_on H' b
      (λa, is_contr.mk a
        (λa',
          fiber_eq ((ap f)⁻¹ ((point_eq a) ⬝ (point_eq a')⁻¹))
                   (by rewrite (right_inv (ap f)); rewrite inv_con_cancel_right))))

  definition is_split_surjective_of_is_retraction [H : is_retraction f] : is_split_surjective f :=
  λb, fiber.mk (sect f b) (right_inverse f b)

  definition is_constant_compose_point [constructor] [instance] (b : B)
    : is_constant (f ∘ point : fiber f b → B) :=
  is_constant.mk b (λv, by induction v with a p;exact p)

  definition is_embedding_of_is_hprop_fiber [H : Π(b : B), is_hprop (fiber f b)] : is_embedding f :=
  begin
    intro a a',
    fapply adjointify,
    { intro p, exact ap point (is_hprop.elim (fiber.mk a p) (fiber.mk a' idp))},
    { exact abstract begin
      intro p, rewrite [-ap_compose],
      apply @is_constant.eq _ _ _ (is_constant_ap (f ∘ point) (fiber.mk a p) (fiber.mk a' idp))
      end end },
    { intro p, induction p, rewrite [▸*,is_hprop_elim_self]},
  end

  -- definition is_embedding_of_is_section_inv' [H : is_section f] {a : A} {b : B} (p : f a = b) :
  --   a = retr f b :=
  -- (left_inverse f a)⁻¹ ⬝ ap (retr f) p

  -- definition is_embedding_of_is_section_inv [H : is_section f] {a a' : A} (p : f a = f a') :
  --   a = a' :=
  -- is_embedding_of_is_section_inv' f p ⬝ left_inverse f a'

  -- definition is_embedding_of_is_section [constructor] [instance] [H : is_section f]
  --   : is_embedding f :=
  -- begin
  --   intro a a',
  --   fapply adjointify,
  --   { exact is_embedding_of_is_section_inv f},
  --   { exact abstract begin
  --     assert H2 : Π {b : B} (p : f a = b), ap f (is_embedding_of_is_section_inv' f p) = p ⬝ _,
  --     { }
  --           -- intro p, rewrite [+ap_con,-ap_compose],
  --           -- check_expr natural_square (left_inverse f),
  --           -- induction H with g q, esimp,
  --           end end },
  --   { intro p, induction p, esimp, apply con.left_inv},
  -- end

  definition is_retraction_of_is_equiv [instance] [H : is_equiv f] : is_retraction f :=
  is_retraction.mk f⁻¹ (right_inv f)

  definition is_section_of_is_equiv [instance] [H : is_equiv f] : is_section f :=
  is_section.mk f⁻¹ (left_inv f)

  definition is_equiv_of_is_section_of_is_retraction [H1 : is_retraction f] [H2 : is_section f]
    : is_equiv f :=
  let g := sect f in let h := retr f in
  adjointify f
             (g)
             (right_inverse f)
             (λa, calc
                    g (f a) = h (f (g (f a))) : left_inverse
                    ... = h (f a) : right_inverse f
                    ... = a : left_inverse)

  section
    local attribute is_equiv_of_is_section_of_is_retraction [instance]
    variable (f)
    definition is_hprop_is_retraction_prod_is_section : is_hprop (is_retraction f × is_section f) :=
    begin
      apply is_hprop_of_imp_is_contr, intro H, induction H with H1 H2,
      exact _,
    end
  end

  variable {f}

  definition is_retraction_trunc_functor [instance] (r : A → B) [H : is_retraction r]
    (n : trunc_index) : is_retraction (trunc_functor n r) :=
  is_retraction.mk
    (trunc_functor n (sect r))
    (λb,
      ((trunc_functor_compose n (sect r) r) b)⁻¹
      ⬝ trunc_homotopy n (right_inverse r) b
      ⬝ trunc_functor_id B n b)

  -- Lemma 3.11.7
  definition is_contr_retract (r : A → B) [H : is_retraction r] : is_contr A → is_contr B :=
  begin
    intro CA,
    apply is_contr.mk (r (center A)),
    intro b,
    exact ap r (center_eq (is_retraction.sect r b)) ⬝ (is_retraction.right_inverse r b)
  end

  local attribute is_hprop_is_retraction_prod_is_section [instance]
  definition is_retraction_prod_is_section_equiv_is_equiv
    : (is_retraction f × is_section f) ≃ is_equiv f :=
  begin
    apply equiv_of_is_hprop,
    intro H, induction H, apply is_equiv_of_is_section_of_is_retraction,
    intro H, split, repeat exact _
  end

  /-
    The definitions
      is_surjective_of_is_equiv
      is_equiv_equiv_is_embedding_times_is_surjective
    are in types.trunc
  -/

end function
