/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.num

structure sigma {A : Type} (B : A → Type) :=
mk :: (pr1 : A) (pr2 : B pr1)

notation `Σ` binders `,` r:(scoped P, sigma P) := r

namespace sigma
  notation `pr₁` := pr1
  notation `pr₂` := pr2
  notation `⟨`:max t:(foldr `,` (e r, mk e r)) `⟩`:0 := t --input ⟨ ⟩ as \< \>

  namespace ops
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2
  end ops
end sigma
