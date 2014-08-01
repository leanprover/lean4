----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.classes.inhabited

variable epsilon {A : Type} {H : inhabited A} (P : A → Prop) : A
axiom epsilon_ax {A : Type} {P : A → Prop} (Hex : ∃ a, P a) : P (@epsilon A (inhabited_exists Hex) P)

theorem epsilon_singleton {A : Type} (a : A) : @epsilon A (inhabited_intro a) (λ x, x = a) = a :=
epsilon_ax (exists_intro a (refl a))

theorem axiom_of_choice {A : Type} {B : A → Type} {R : Π x, B x → Prop} (H : ∀ x, ∃ y, R x y) : ∃ f, ∀ x, R x (f x) :=
let f [inline] := λ x, @epsilon _ (inhabited_exists (H x)) (λ y, R x y),
    H [inline] := take x, epsilon_ax (H x)
in exists_intro f H

theorem skolem {A : Type} {B : A → Type} {P : Π x, B x → Prop} : (∀ x, ∃ y, P x y) ↔ ∃ f, (∀ x, P x (f x)) :=
iff_intro
  (assume H : (∀ x, ∃ y, P x y), axiom_of_choice H)
  (assume H : (∃ f, (∀ x, P x (f x))),
    take x, obtain (fw : ∀ x, B x) (Hw : ∀ x, P x (fw x)), from H,
      exists_intro (fw x) (Hw x))
