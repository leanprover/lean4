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

  -- prod.eta is already used for the eta rule for strict equality
  protected definition peta (u : A × B) : (pr₁ u , pr₂ u) ≈ u :=
  destruct u (λu1 u2, idp)

  definition pair_path (pa : a ≈ a') (pb : b ≈ b') : (a , b) ≈ (a' , b') :=
  path.rec_on pa (path.rec_on pb idp)

  protected definition path : (pr₁ u ≈ pr₁ v) → (pr₂ u ≈ pr₂ v) → u ≈ v :=
  begin
    apply (prod.rec_on u), intros (a₁, b₁),
    apply (prod.rec_on v), intros (a₂, b₂, H₁, H₂),
    apply (transport _ (peta (a₁, b₁))),
    apply (transport _ (peta (a₂, b₂))),
    apply (pair_path H₁ H₂),
  end

  /- Symmetry -/

  definition isequiv_flip [instance] (A B : Type) : is_equiv (@flip A B) :=
  adjointify flip
             flip
             (λu, destruct u (λb a, idp))
             (λu, destruct u (λa b, idp))

  definition symm_equiv (A B : Type) : A × B ≃ B × A :=
  equiv.mk flip _

  -- trunc_prod is defined in sigma

end prod
