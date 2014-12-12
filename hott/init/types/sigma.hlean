/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import ..num ..wf ..logic ..tactic

structure sigma {A : Type} (B : A → Type) :=
dpair :: (dpr1 : A) (dpr2 : B dpr1)

notation `Σ` binders `,` r:(scoped P, sigma P) := r

namespace sigma

  notation `dpr₁` := dpr1
  notation `dpr₂` := dpr2

  namespace ops
  postfix `.1`:(max+1) := dpr1
  postfix `.2`:(max+1) := dpr2
  notation `⟨` t:(foldr `,` (e r, sigma.dpair e r)) `⟩`:0 := t --input ⟨ ⟩ as \< \>
  end ops

end sigma
