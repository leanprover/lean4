/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Opposite precategory and (TODO) category
-/

import ..functor ..category

open eq functor

namespace category

  definition opposite [reducible] [constructor] {ob : Type} (C : precategory ob) : precategory ob :=
  precategory.mk' (λ a b, hom b a)
                  (λ a b c f g, g ∘ f)
                  (λ a, id)
                  (λ a b c d f g h, !assoc')
                  (λ a b c d f g h, !assoc)
                  (λ a b f, !id_right)
                  (λ a b f, !id_left)
                  (λ a, !id_id)
                  (λ a b, !is_hset_hom)

  definition Opposite [reducible] [constructor] (C : Precategory) : Precategory :=
  precategory.Mk (opposite C)

  infixr `∘op`:60 := @comp _ (opposite _) _ _ _
  postfix `ᵒᵖ`:(max+2) := Opposite

  variables {C : Precategory} {a b c : C}

  definition compose_op {f : hom a b} {g : hom b c} : f ∘op g = g ∘ f :=
  by reflexivity

  definition opposite_opposite' {ob : Type} (C : precategory ob) : opposite (opposite C) = C :=
  by cases C; apply idp

  definition opposite_opposite : (Cᵒᵖ)ᵒᵖ = C :=
  (ap (Precategory.mk C) (opposite_opposite' C)) ⬝ !Precategory.eta


  definition opposite_functor [reducible] {C D : Precategory} (F : C ⇒ D) : Cᵒᵖ ⇒ Dᵒᵖ :=
  begin
    apply (@functor.mk (Cᵒᵖ) (Dᵒᵖ)),
      intro a, apply (respect_id F),
      intros, apply (@respect_comp C D)
  end

  postfix `ᵒᵖ`:(max+2) := opposite_functor

end category
