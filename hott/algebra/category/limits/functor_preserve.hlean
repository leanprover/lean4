/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Functors preserving limits
-/

import .colimits ..functor.yoneda

open eq functor yoneda is_trunc nat_trans

namespace category

  variables {I C D : Precategory} {F : I ⇒ C} {G : C ⇒ D}

  /- notions of preservation of limits -/
  definition preserves_limits_of_shape [class] (G : C ⇒ D) (I : Precategory)
    [H : has_limits_of_shape C I] :=
  Π(F : I ⇒ C), is_terminal (cone_obj_compose G (limit_cone F))

  definition preserves_existing_limits_of_shape [class] (G : C ⇒ D) (I : Precategory) :=
  Π(F : I ⇒ C) [H : has_terminal_object (cone F)],
    is_terminal (cone_obj_compose G (terminal_object (cone F)))

  definition preserves_existing_limits [class] (G : C ⇒ D) :=
  Π(I : Precategory) (F : I ⇒ C) [H : has_terminal_object (cone F)],
    is_terminal (cone_obj_compose G (terminal_object (cone F)))

  definition preserves_limits [class] (G : C ⇒ D) [H : is_complete C] :=
  Π(I : Precategory) [H : has_limits_of_shape C I] (F : I ⇒ C),
    is_terminal (cone_obj_compose G (limit_cone F))

  definition preserves_chosen_limits_of_shape [class] (G : C ⇒ D) (I : Precategory)
    [H : has_limits_of_shape C I] [H : has_limits_of_shape D I] :=
  Π(F : I ⇒ C), cone_obj_compose G (limit_cone F) = limit_cone (G ∘f F)

  definition preserves_chosen_limits [class] (G : C ⇒ D)
    [H : is_complete C] [H : is_complete D] :=
  Π(I : Precategory) (F : I ⇒ C), cone_obj_compose G (limit_cone F) = limit_cone (G ∘f F)

  /- basic instances -/
  definition preserves_limits_of_shape_of_preserves_limits [instance] (G : C ⇒ D)
    (I : Precategory) [H : is_complete C] [H : preserves_limits G]
    : preserves_limits_of_shape G I := H I

  definition preserves_chosen_limits_of_shape_of_preserves_chosen_limits [instance] (G : C ⇒ D)
    (I : Precategory) [H : is_complete C] [H : is_complete D] [K : preserves_chosen_limits G]
    : preserves_chosen_limits_of_shape G I := K I

  /- yoneda preserves existing limits -/

  local attribute Category.to.precategory category.to_precategory [constructor]

  definition preserves_existing_limits_yoneda_embedding_lemma [constructor] (y : cone_obj F)
    [H : is_terminal y] {G : Cᵒᵖ ⇒ cset} (η : constant_functor I G ⟹ ɏ ∘f F) :
    G ⟹ hom_functor_left (cone_to_obj y) :=
  begin
    fapply nat_trans.mk: esimp,
    { intro c x, fapply to_hom_limit,
      { intro i, exact η i c x},
      { exact abstract begin
        intro i j k,
        exact !id_right⁻¹ ⬝ !assoc⁻¹ ⬝ ap0100 natural_map (naturality η k) c x end end
        }},
      -- [BUG] abstracting here creates multiple lemmas proving this fact
    { intro c c' f, apply eq_of_homotopy, intro x,
      rewrite [id_left], apply to_eq_hom_limit, intro i,
      refine !assoc ⬝ _, rewrite to_hom_limit_commute,
      refine _ ⬝ ap10 (naturality (η i) f) x, rewrite [▸*, id_left]}
      -- abstracting here fails
  end
--  print preserves_existing_limits_yoneda_embedding_lemma_11

  theorem preserves_existing_limits_yoneda_embedding (C : Precategory)
    : preserves_existing_limits (yoneda_embedding C) :=
  begin
    intro I F H Gη, induction H with y H, induction Gη with G η, esimp at *,
    assert lem : Π (i : carrier I),
    nat_trans_hom_functor_left (natural_map (cone_to_nat y) i)
      ∘n preserves_existing_limits_yoneda_embedding_lemma y η = natural_map η i,
    { intro i, apply nat_trans_eq, intro c, apply eq_of_homotopy, intro x,
        esimp, refine !assoc ⬝ !id_right ⬝ !to_hom_limit_commute},
    fapply is_contr.mk,
    { fapply cone_hom.mk,
      { exact preserves_existing_limits_yoneda_embedding_lemma y η},
      { exact lem}},
    { intro v, apply cone_hom_eq, esimp, apply nat_trans_eq, esimp, intro c,
      apply eq_of_homotopy, intro x, refine (to_eq_hom_limit _ _)⁻¹,
      intro i, refine !id_right⁻¹ ⬝ !assoc⁻¹ ⬝ _,
      exact ap0100 natural_map (cone_to_eq v i) c x}
  end

end category
