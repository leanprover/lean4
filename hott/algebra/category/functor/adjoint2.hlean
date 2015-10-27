/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

TODO: merge with adjoint
-/

import .adjoint .examples

open eq functor nat_trans iso prod is_trunc

namespace category

  section
  universe variables u v
  parameters {C D : Precategory.{u v}} {F : C ⇒ D} {G : D ⇒ C}
          (θ : hom_functor D ∘f prod_functor_prod Fᵒᵖᶠ 1 ≅ hom_functor C ∘f prod_functor_prod 1 G)
  include θ
  /- θ : _ ⟹[Cᵒᵖ × D ⇒ set] _-/

  definition adj_unit [constructor] : 1 ⟹ G ∘f F :=
  begin
    fapply nat_trans.mk: esimp,
    { intro c, exact natural_map (to_hom θ) (c, F c) id},
    { intro c c' f,
      let H := naturality (to_hom θ) (ID c, F f),
      let K := ap10 H id,
      rewrite [▸* at K, id_right at K, ▸*, K, respect_id, +id_right],
      clear H K,
      let H := naturality (to_hom θ) (f, ID (F c')),
      let K := ap10 H id,
      rewrite [▸* at K, respect_id at K,+id_left at K, K]}
  end

  definition adj_counit [constructor] : F ∘f G ⟹ 1 :=
  begin
    fapply nat_trans.mk: esimp,
    { intro d, exact natural_map (to_inv θ) (G d, d) id, },
    { intro d d' g,
      let H := naturality (to_inv θ) (Gᵒᵖᶠ g, ID d'),
      let K := ap10 H id,
      rewrite [▸* at K, id_left at K, ▸*, K, respect_id, +id_left],
      clear H K,
      let H := naturality (to_inv θ) (ID (G d), g),
      let K := ap10 H id,
      rewrite [▸* at K, respect_id at K,+id_right at K, K]}
  end

  theorem adj_eq_unit (c : C) (d : D) (f : F c ⟶ d)
    : natural_map (to_hom θ) (c, d) f = G f ∘ adj_unit c :=
  begin
    esimp,
    let H := naturality (to_hom θ) (ID c, f),
    let K := ap10 H id,
    rewrite [▸* at K, id_right at K, K, respect_id, +id_right],
  end

  theorem adj_eq_counit (c : C) (d : D) (g : c ⟶ G d)
    : natural_map (to_inv θ) (c, d) g = adj_counit d ∘ F g :=
  begin
    esimp,
    let H := naturality (to_inv θ) (g, ID d),
    let K := ap10 H id,
    rewrite [▸* at K, id_left at K, K, respect_id, +id_left],
  end

  definition adjoint.mk' [constructor] : F ⊣ G :=
  begin
    fapply adjoint.mk,
    { exact adj_unit},
    { exact adj_counit},
    { intro c, esimp, refine (adj_eq_counit c (F c) (adj_unit c))⁻¹ ⬝ _,
      apply ap10 (to_left_inverse (componentwise_iso θ (c, F c)))},
    { intro d, esimp, refine (adj_eq_unit (G d) d (adj_counit d))⁻¹ ⬝ _,
      apply ap10 (to_right_inverse (componentwise_iso θ (G d, d)))},
  end

  end



end category
