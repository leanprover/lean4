----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad
----------------------------------------------------------------------------------------------------

import .basic .eq

inductive Exists {A : Type} (P : A → Prop) : Prop :=
| exists_intro : ∀ (a : A), P a → Exists P

notation `exists` binders `,` r:(scoped P, Exists P) := r
notation `∃` binders `,` r:(scoped P, Exists P) := r

theorem exists_elim {A : Type} {p : A → Prop} {B : Prop} (H1 : ∃x, p x) (H2 : ∀ (a : A) (H : p a), B) : B :=
Exists_rec H2 H1

theorem exists_not_forall {A : Type} {p : A → Prop} (H : ∃x, p x) : ¬∀x, ¬p x :=
assume H1 : ∀x, ¬p x,
  obtain (w : A) (Hw : p w), from H,
  absurd Hw (H1 w)

theorem forall_not_exists {A : Type} {p : A → Prop} (H2 : ∀x, p x) : ¬∃x, ¬p x :=
assume H1 : ∃x, ¬p x,
  obtain (w : A) (Hw : ¬p w), from H1,
  absurd (H2 w) Hw

definition exists_unique {A : Type} (p : A → Prop) :=
∃x, p x ∧ ∀y, y ≠ x → ¬p y

notation `∃!` binders `,` r:(scoped P, exists_unique P) := r

theorem exists_unique_intro {A : Type} {p : A → Prop} (w : A) (H1 : p w) (H2 : ∀y, y ≠ w → ¬p y) : ∃!x, p x :=
exists_intro w (and_intro H1 H2)

theorem exists_unique_elim {A : Type} {p : A → Prop} {b : Prop}
                           (H2 : ∃!x, p x) (H1 : ∀x, p x → (∀y, y ≠ x → ¬p y) → b) : b :=
obtain w Hw, from H2,
H1 w (and_elim_left Hw) (and_elim_right Hw)
