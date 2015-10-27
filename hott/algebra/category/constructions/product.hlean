/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Product precategory and (TODO) category
-/

import ..category ..nat_trans hit.trunc

open eq prod is_trunc functor sigma trunc iso prod.ops nat_trans

namespace category
  definition precategory_prod [constructor] [reducible] [instance] (obC obD : Type)
    [C : precategory obC] [D : precategory obD] : precategory (obC × obD) :=
  precategory.mk' (λ a b, hom a.1 b.1 × hom a.2 b.2)
                  (λ a b c g f, (g.1 ∘ f.1, g.2 ∘ f.2))
                  (λ a, (id, id))
                  (λ a b c d h g f, pair_eq !assoc    !assoc   )
                  (λ a b c d h g f, pair_eq !assoc'   !assoc'  )
                  (λ a b f,         prod_eq !id_left  !id_left )
                  (λ a b f,         prod_eq !id_right !id_right)
                  (λ a,             prod_eq !id_id    !id_id)
                  _

  definition Precategory_prod [reducible] [constructor] (C D : Precategory) : Precategory :=
  precategory.Mk (precategory_prod C D)

  infixr ` ×c `:70 := Precategory_prod

  variables {C C' D D' X : Precategory} {u v : carrier (C ×c D)}

  theorem prod_hom_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : hom_of_eq (prod_eq p q) = (hom_of_eq p, hom_of_eq q) :=
  by induction u; induction v; esimp at *; induction p; induction q; reflexivity

  theorem prod_inv_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : inv_of_eq (prod_eq p q) = (inv_of_eq p, inv_of_eq q) :=
  by induction u; induction v; esimp at *; induction p; induction q; reflexivity

  theorem pr1_hom_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : (hom_of_eq (prod_eq p q)).1 = hom_of_eq p :=
  by exact ap pr1 !prod_hom_of_eq

  theorem pr1_inv_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : (inv_of_eq (prod_eq p q)).1 = inv_of_eq p :=
  by exact ap pr1 !prod_inv_of_eq

  theorem pr2_hom_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : (hom_of_eq (prod_eq p q)).2 = hom_of_eq q :=
  by exact ap pr2 !prod_hom_of_eq

  theorem pr2_inv_of_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : (inv_of_eq (prod_eq p q)).2 = inv_of_eq q :=
  by exact ap pr2 !prod_inv_of_eq

  definition pr1_functor [constructor] : C ×c D ⇒ C :=
  functor.mk pr1
             (λa b, pr1)
             (λa, idp)
             (λa b c g f, idp)

  definition pr2_functor [constructor] : C ×c D ⇒ D :=
  functor.mk pr2
             (λa b, pr2)
             (λa, idp)
             (λa b c g f, idp)

  definition functor_prod [constructor] [reducible] (F : X ⇒ C) (G : X ⇒ D) : X ⇒ C ×c D :=
  functor.mk (λ a,     pair (F a) (G a))
             (λ a b f, pair (F f) (G f))
             (λ a,         abstract pair_eq !respect_id   !respect_id   end)
             (λ a b c g f, abstract pair_eq !respect_comp !respect_comp end)

  infixr ` ×f `:70 := functor_prod

  definition prod_functor_eta (F : X ⇒ C ×c D) : pr1_functor ∘f F ×f pr2_functor ∘f F = F :=
  begin
  fapply functor_eq: esimp,
  { intro e, apply prod_eq: reflexivity},
  { intro e e' f, apply prod_eq: esimp,
    { refine ap (λx, x ∘ _ ∘ _) !pr1_hom_of_eq ⬝ _,
      refine ap (λx, _ ∘ _ ∘ x) !pr1_inv_of_eq ⬝ _, esimp,
      apply id_leftright},
    { refine ap (λx, x ∘ _ ∘ _) !pr2_hom_of_eq ⬝ _,
      refine ap (λx, _ ∘ _ ∘ x) !pr2_inv_of_eq ⬝ _, esimp,
      apply id_leftright}}
  end

  definition pr1_functor_prod (F : X ⇒ C) (G : X ⇒ D) : pr1_functor ∘f (F ×f G) = F :=
  functor_eq (λx, idp)
             (λx y f, !id_leftright)

  definition pr2_functor_prod (F : X ⇒ C) (G : X ⇒ D) : pr2_functor ∘f (F ×f G) = G :=
  functor_eq (λx, idp)
             (λx y f, !id_leftright)

  -- definition universal_property_prod {C D X : Precategory} (F : X ⇒ C) (G : X ⇒ D)
  --   : is_contr (Σ(H : X ⇒ C ×c D), pr1_functor ∘f H = F × pr2_functor ∘f H = G) :=
  -- is_contr.mk
  --   ⟨functor_prod F G, (pr1_functor_prod F G, pr2_functor_prod F G)⟩
  --   begin
  --     intro v, induction v with H w, induction w with p q,
  --     symmetry, fapply sigma_eq: esimp,
  --     { fapply functor_eq,
  --       { intro x, apply prod_eq: esimp,
  --         { exact ap010 to_fun_ob p x},
  --         { exact ap010 to_fun_ob q x}},
  --       { intro x y f, apply prod_eq: esimp,
  --         { exact sorry},
  --         { exact sorry}}},
  --     { exact sorry}
  --   end

  definition prod_functor_prod [constructor] (F : C ⇒ D) (G : C' ⇒ D') : C ×c C' ⇒ D ×c D' :=
  (F ∘f pr1_functor) ×f (G ∘f pr2_functor)

  definition prod_nat_trans [constructor] {C D D' : Precategory}
    {F F' : C ⇒ D} {G G' : C ⇒ D'} (η : F ⟹ F') (θ : G ⟹ G') : F ×f G ⟹ F' ×f G' :=
  begin
    fapply nat_trans.mk: esimp,
    { intro c, exact (η c, θ c)},
    { intro c c' f, apply prod_eq: esimp:apply naturality}
  end

  infixr ` ×n `:70 := prod_nat_trans

  definition prod_flip_functor [constructor] (C D : Precategory) : C ×c D ⇒ D ×c C :=
  functor.mk (λp, (p.2, p.1))
             (λp p' h, (h.2, h.1))
             (λp, idp)
             (λp p' p'' h' h, idp)

  definition functor_prod_flip_functor_prod_flip (C D : Precategory)
    : prod_flip_functor D C ∘f (prod_flip_functor C D) = functor.id :=
  begin
  fapply functor_eq,
  { intro p, apply prod.eta},
  { intro p p' h, cases p with c d, cases p' with c' d',
    apply id_leftright}
  end

end category
