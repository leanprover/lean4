/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
Ported from Coq HoTT

Theorems about products
-/

import ..trunc data.prod
open path equiv is_equiv truncation prod

variables {A A' B B' C D : Type}
          {a a' a'' : A} {b b₁ b₂ b' b'' : B} {u v w : A × B}

namespace prod

  definition eta_prod (u : A × B) : (pr₁ u , pr₂ u) ≈ u :=
  destruct u (λu1 u2, idp)

  definition pair_path (pa : a ≈ a') (pb : b ≈ b') : (a , b) ≈ (a' , b') :=
  path.rec_on pa (path.rec_on pb idp)

  protected definition path : (pr₁ u ≈ pr₁ v) → (pr₂ u ≈ pr₂ v) → u ≈ v :=
  begin
    apply (prod.rec_on u), intros (a₁, b₁),
    apply (prod.rec_on v), intros (a₂, b₂, H₁, H₂),
    apply (transport _ (eta_prod (a₁, b₁))),
    apply (transport _ (eta_prod (a₂, b₂))),
    apply (pair_path H₁ H₂),
  end

  /- Symmetry -/

  definition isequiv_prod_symm [instance] (A B : Type) : is_equiv (@flip A B) :=
  adjointify flip
             flip
             (λu, destruct u (λb a, idp))
             (λu, destruct u (λa b, idp))

  definition equiv_prod_symm (A B : Type) : A × B ≃ B × A :=
  equiv.mk flip _

  -- Pairs preserve truncatedness
  definition trunc_prod [instance] {A B : Type} (n : trunc_index) :
      (is_trunc n A) → (is_trunc n B) → is_trunc n (A × B)
    := sorry --Assignment for Floris

end prod
