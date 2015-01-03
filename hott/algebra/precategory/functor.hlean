-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Floris van Doorn, Jakob von Raumer

import .basic types.pi

open function precategory eq prod equiv is_equiv sigma sigma.ops truncation
open pi

structure functor (C D : Precategory) : Type :=
  (obF : C → D)
  (homF : Π ⦃a b : C⦄, hom a b → hom (obF a) (obF b))
  (respect_id : Π (a : C), homF (ID a) = ID (obF a))
  (respect_comp : Π {a b c : C} (g : hom b c) (f : hom a b),
    homF (g ∘ f) = homF g ∘ homF f)

infixl `⇒`:25 := functor

namespace functor
  variables {C D E : Precategory}

  coercion [persistent] obF
  coercion [persistent] homF

  -- "functor C D" is equivalent to a certain sigma type
  set_option unifier.max_steps 38500
  protected definition sigma_char :
    (Σ (obF : C → D)
    (homF : Π ⦃a b : C⦄, hom a b → hom (obF a) (obF b)),
    (Π (a : C), homF (ID a) = ID (obF a)) ×
    (Π {a b c : C} (g : hom b c) (f : hom a b),
      homF (g ∘ f) = homF g ∘ homF f)) ≃ (functor C D) :=
  begin
    fapply equiv.mk,
      intro S, fapply functor.mk,
        exact (S.1), exact (S.2.1),
        exact (pr₁ S.2.2), exact (pr₂ S.2.2),
    fapply adjointify,
      intro F, apply (functor.rec_on F), intros (d1, d2, d3, d4),
      exact (sigma.mk d1 (sigma.mk d2 (pair d3 (@d4)))),
    intro F, apply (functor.rec_on F), intros (d1, d2, d3, d4), apply idp,
    intro S, apply (sigma.rec_on S), intros (d1, S2),
    apply (sigma.rec_on S2), intros (d2, P1),
    apply (prod.rec_on P1), intros (d3, d4), apply idp,
  end

  protected definition strict_cat_has_functor_hset
    [HD : is_hset (objects D)] : is_hset (functor C D) :=
  begin
    apply trunc_equiv, apply equiv.to_is_equiv,
      apply sigma_char,
    apply trunc_sigma, apply trunc_pi, intros, exact HD, intro F,
    apply trunc_sigma, apply trunc_pi, intro a,
      apply trunc_pi, intro b,
      apply trunc_pi, intro c, apply !homH,
    intro H, apply trunc_prod,
      apply trunc_pi, intro a,
      apply succ_is_trunc, apply trunc_succ, apply !homH,
    apply trunc_pi, intro a,
    apply trunc_pi, intro b,
    apply trunc_pi, intro c,
    apply trunc_pi, intro g,
    apply trunc_pi, intro f,
      apply succ_is_trunc, apply trunc_succ, apply !homH,
  end

  -- The following lemmas will later be used to prove that the type of
  -- precategories formes a precategory itself
  protected definition compose (G : functor D E) (F : functor C D) : functor C E :=
  functor.mk
    (λ x, G (F x))
    (λ a b f, G (F f))
    (λ a, calc
      G (F (ID a)) = G (ID (F a)) : {respect_id F a}
               ... = ID (G (F a)) : respect_id G (F a))
    (λ a b c g f, calc
      G (F (g ∘ f)) = G (F g ∘ F f)     : respect_comp F g f
                ... = G (F g) ∘ G (F f) : respect_comp G (F g) (F f))

  infixr `∘f`:60 := compose



  protected theorem congr
    {C : Precategory} {D : Precategory}
    (F : C → D)
    (foo2 : Π ⦃a b : C⦄, hom a b → hom (F a) (F b))
    (foo3a foo3b : Π (a : C), foo2 (ID a) = ID (F a))
    (foo4a foo4b : Π {a b c : C} (g : @hom C C b c) (f : @hom C C a b),
      foo2 (g ∘ f) = foo2 g ∘ foo2 f)
    (p3 : foo3a = foo3b) (p4 : @foo4a = @foo4b)
      : functor.mk F foo2 foo3a @foo4a = functor.mk F foo2 foo3b @foo4b
  :=
  begin
    apply (eq.rec_on p3), intros,
    apply (eq.rec_on p4), intros,
    apply idp,
  end

  protected theorem assoc {A B C D : Precategory} (H : functor C D) (G : functor B C) (F : functor A B) :
      H ∘f (G ∘f F) = (H ∘f G) ∘f F :=
  begin
    apply (functor.rec_on H), intros (H1, H2, H3, H4),
    apply (functor.rec_on G), intros (G1, G2, G3, G4),
    apply (functor.rec_on F), intros (F1, F2, F3, F4),
    fapply functor.congr,
      apply funext.path_pi, intro a,
      apply (@is_hset.elim), apply !homH,
    apply funext.path_pi, intro a,
    repeat (apply funext.path_pi; intros),
    apply (@is_hset.elim), apply !homH,
  end

  protected definition id {C : Precategory} : functor C C :=
  mk (λa, a) (λ a b f, f) (λ a, idp) (λ a b c f g, idp)

  protected definition ID (C : Precategory) : functor C C := id

  protected theorem id_left  (F : functor C D) : id ∘f F = F :=
  begin
    apply (functor.rec_on F), intros (F1, F2, F3, F4),
    fapply functor.congr,
      apply funext.path_pi, intro a,
      apply (@is_hset.elim), apply !homH,
    repeat (apply funext.path_pi; intros),
    apply (@is_hset.elim), apply !homH,
  end

  protected theorem id_right (F : functor C D) : F ∘f id = F :=
  begin
    apply (functor.rec_on F), intros (F1, F2, F3, F4),
    fapply functor.congr,
      apply funext.path_pi, intro a,
      apply (@is_hset.elim), apply !homH,
    repeat (apply funext.path_pi; intros),
    apply (@is_hset.elim), apply !homH,
  end

end functor


namespace precategory
  open functor

  definition precat_of_strict_precats : precategory (Σ (C : Precategory), is_hset (objects C)) :=
  precategory.mk (λ a b, functor a.1 b.1)
     (λ a b, @functor.strict_cat_has_functor_hset a.1 b.1 b.2)
     (λ a b c g f, functor.compose g f)
     (λ a, functor.id)
     (λ a b c d h g f, !functor.assoc)
     (λ a b f, !functor.id_left)
     (λ a b f, !functor.id_right)

  definition Precat_of_strict_cats := Mk precat_of_strict_precats

  namespace ops

    notation `PreCat`:max := Precat_of_strict_cats
    instance [persistent] precat_of_strict_precats

  end ops

end precategory

namespace functor
--  open category.ops
--   universes l m
   variables {C D : Precategory}
--   check hom C D
--   variables (F : C ⟶ D) (G : D ⇒ C)
--   check G ∘ F
--   check F ∘f G
--   variables (a b : C) (f : a ⟶ b)
--   check F a
--   check F b
--   check F f
--   check G (F f)
--   print "---"
-- --  check (G ∘ F) f --error
--   check (λ(x : functor C C), x) (G ∘ F) f
--   check (G ∘f F) f
--   print "---"
-- --  check (G ∘ F) a --error
--   check (G ∘f F) a
--   print "---"
-- --  check λ(H : hom C D) (x : C), H x  --error
--   check λ(H : @hom _ Cat C D) (x : C), H x
--   check λ(H : C ⇒ D) (x : C), H x
--   print "---"
--   -- variables {obF obG : C → D} (Hob : ∀x, obF x = obG x) (homF : Π(a b : C) (f : a ⟶ b), obF a ⟶ obF b) (homG : Π(a b : C) (f : a ⟶ b), obG a ⟶ obG b)
-- --  check eq.rec_on (funext Hob) homF = homG

  /-theorem mk_heq {obF obG : C → D} {homF homG idF idG compF compG} (Hob : ∀x, obF x = obG x)
     (Hmor : ∀(a b : C) (f : a ⟶ b), homF a b f == homG a b f)
       : mk obF homF idF compF = mk obG homG idG compG :=
  hddcongr_arg4 mk
              (funext Hob)
              (hfunext (λ a, hfunext (λ b, hfunext (λ f, !Hmor))))
              !proof_irrel
              !proof_irrel

  protected theorem hequal {F G : C ⇒ D} : Π (Hob : ∀x, F x = G x)
      (Hmor : ∀a b (f : a ⟶ b), F f == G f), F = G :=
  functor.rec
    (λ obF homF idF compF,
      functor.rec
        (λ obG homG idG compG Hob Hmor, mk_heq Hob Hmor)
      G)
    F-/

--   theorem mk_eq {obF obG : C → D} {homF homG idF idG compF compG} (Hob : ∀x, obF x = obG x)
--      (Hmor : ∀(a b : C) (f : a ⟶ b), cast (congr_arg (λ x, x a ⟶ x b) (funext Hob)) (homF a b f)
--                                        = homG a b f)
--        : mk obF homF idF compF = mk obG homG idG compG :=
--   dcongr_arg4 mk
--               (funext Hob)
--               (funext (λ a, funext (λ b, funext (λ f, sorry ⬝ Hmor a b f))))
-- -- to fill this sorry use (a generalization of) cast_pull
--               !proof_irrel
--               !proof_irrel

--   protected theorem equal {F G : C ⇒ D} : Π (Hob : ∀x, F x = G x)
--       (Hmor : ∀a b (f : a ⟶ b), cast (congr_arg (λ x, x a ⟶ x b) (funext Hob)) (F f) = G f), F = G :=
--   functor.rec
--     (λ obF homF idF compF,
--       functor.rec
--         (λ obG homG idG compG Hob Hmor, mk_eq Hob Hmor)
--       G)
--     F


end functor
