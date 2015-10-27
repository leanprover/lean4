/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Functors preserving limits
-/

import ..colimits ..yoneda

open functor yoneda is_trunc nat_trans

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

  definition preserves_existing_limits_yoneda_embedding_lemma [constructor] (x : cone_obj F)
    [H : is_terminal x] {G : Cᵒᵖ ⇒ cset} (η : constant_functor I G ⟹ ɏ ∘f F) :
    G ⟹ to_fun_ob ɏ (cone_to_obj x) :=
  begin
    fapply nat_trans.mk: esimp,
    { intro c x, fapply to_hom_limit,
      { intro i, exact η i c x},
      { intro i j k, exact sorry}},
    { intro c c' f, apply eq_of_homotopy, intro x, exact sorry}
  end

  theorem preserves_existing_limits_yoneda_embedding (C : Precategory)
    : preserves_existing_limits (yoneda_embedding C) :=
  begin
    intro I F H Gη, induction H with x H, induction Gη with G η, esimp at *,
    fapply is_contr.mk,
    { fapply cone_hom.mk: esimp,
      { exact sorry
        -- fapply nat_trans.mk: esimp,
        -- { intro c x, esimp [yoneda_embedding], fapply to_hom_limit,
        --   { apply has_terminal_object.is_terminal}, --this should be solved by type class res.
        --   { intro i, induction dη with d η, esimp at *, },
        --   {  intro i j k, }},
        -- { }
  },
      { exact sorry}},
    { exact sorry}
  end

end category
