----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.connectives.eq logic.connectives.function
using function

-- Function extensionality
axiom funext : ∀ {A : Type} {B : A → Type} {f g : Π x, B x} (H : ∀ x, f x = g x), f = g

namespace function
section
  parameters {A : Type} {B : Type} {C : Type} {D : Type}
  theorem compose_assoc (f : C → D) (g : B → C) (h : A → B) : (f ∘ g) ∘ h = f ∘ (g ∘ h) :=
  funext (take x, refl _)

  theorem compose_id_left (f : A → B) : id ∘ f = f :=
  funext (take x, refl _)

  theorem compose_id_right (f : A → B) : f ∘ id = f :=
  funext (take x, refl _)

  theorem compose_const_right (f : B → C) (b : B) : f ∘ (const A b) = const A (f b) :=
  funext (take x, refl _)
end end