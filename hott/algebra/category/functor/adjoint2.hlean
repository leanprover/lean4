
import .equivalence

open eq functor nat_trans

namespace category

  variables {C D E : Precategory} (F : C ⇒ D) (G : D ⇒ C) (H : D ≅c E)
/-
  definition adjoint_compose [constructor] (K : F ⊣ G)
    : H ∘f F ⊣ G ∘f H⁻¹ᴱ :=
  begin
    fconstructor,
    { fapply change_natural_map,
      { exact calc
          1 ⟹ G ∘f F                 : to_unit K
        ... ⟹ (G ∘f 1) ∘f F          : !id_right_natural_rev ∘nf F
        ... ⟹ (G ∘f (H⁻¹ ∘f H)) ∘f F : (G ∘fn unit H) ∘nf F
        ... ⟹ ((G ∘f H⁻¹) ∘f H) ∘f F : !assoc_natural ∘nf F
        ... ⟹ (G ∘f H⁻¹) ∘f (H ∘f F) : assoc_natural_rev},
      { intro c, esimp, exact G (unit H (F c)) ∘ to_unit K c},
      { intro c, rewrite [▸*, +id_left]}},
    { fapply change_natural_map,
      { exact calc
        (H ∘f F) ∘f (G ∘f H⁻¹)
            ⟹ ((H ∘f F) ∘f G) ∘f H⁻¹ : assoc_natural
        ... ⟹ (H ∘f (F ∘f G)) ∘f H⁻¹ : !assoc_natural_rev ∘nf H⁻¹
        ... ⟹ (H ∘f 1) ∘f H⁻¹        : (H ∘fn to_counit K) ∘nf H⁻¹
        ... ⟹ H ∘f H⁻¹               : !id_right_natural ∘nf H⁻¹
        ... ⟹ 1                      : counit H},
      { intro e, esimp, exact counit H e ∘ to_fun_hom H (to_counit K (H⁻¹ e))},
      { intro c, rewrite [▸*, +id_right, +id_left]}},
    { intro c, rewrite [▸*, +respect_comp], refine !assoc ⬝ ap (λx, x ∘ _) !assoc⁻¹ ⬝ _,
      rewrite [-respect_comp],
      },
    { }
  end
-/
end category
