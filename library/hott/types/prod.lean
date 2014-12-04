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


  /- Symmetry -/

  definition isequiv_prod_symm [instance] (A B : Type) : is_equiv (@flip A B) :=
  adjointify flip
             flip
             (λu, destruct u (λb a, idp))
             (λu, destruct u (λa b, idp))

  definition equiv_prod_symm (A B : Type) : A × B ≃ B × A :=
  equiv.mk flip _

end prod
