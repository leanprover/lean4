/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: logic.axioms.funext
Author: Leonardo de Moura

Function extensionality.
-/
import logic.cast algebra.function data.sigma
open function eq.ops

axiom funext : ∀ {A : Type} {B : A → Type} {f g : Π a, B a} (H : ∀ a, f a = g a), f = g

namespace function
  variables {A B C D: Type}

  theorem compose.assoc (f : C → D) (g : B → C) (h : A → B) : (f ∘ g) ∘ h = f ∘ (g ∘ h) :=
  funext (take x, rfl)

  theorem compose.left_id (f : A → B) : id ∘ f = f :=
  funext (take x, rfl)

  theorem compose.right_id (f : A → B) : f ∘ id = f :=
  funext (take x, rfl)

  theorem compose_const_right (f : B → C) (b : B) : f ∘ (const A b) = const A (f b) :=
  funext (take x, rfl)

  theorem hfunext {A : Type} {B : A → Type} {B' : A → Type} {f : Π x, B x} {g : Π x, B' x}
      (H : ∀ a, f a == g a) : f == g :=
  let HH : B = B' := (funext (λ x, heq.type_eq (H x))) in
  cast_to_heq (funext (λ a, heq.to_eq (heq.trans (cast_app HH f a) (H a))))
end function
