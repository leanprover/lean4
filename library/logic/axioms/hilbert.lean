/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

Follows Coq.Logic.ClassicalEpsilon (but our definition of "inhabited" is the constructive one).
-/
import logic.quantifiers
import data.subtype data.sum
open subtype inhabited nonempty

/- the axiom -/

-- In the presence of classical logic, we could prove this from a weaker statement:
-- axiom indefinite_description {A : Type} {P : A->Prop} (H : ∃x, P x) : {x : A, P x}
axiom strong_indefinite_description {A : Type} (P : A → Prop) (H : nonempty A) :
  { x | (∃y : A, P y) → P x}

theorem exists_true_of_nonempty {A : Type} (H : nonempty A) : ∃x : A, true :=
nonempty.elim H (take x, exists.intro x trivial)

theorem inhabited_of_nonempty {A : Type} (H : nonempty A) : inhabited A :=
let u : {x | (∃y : A, true) → true} := strong_indefinite_description (λa, true) H in
inhabited.mk (elt_of u)

theorem inhabited_of_exists {A : Type} {P : A → Prop} (H : ∃x, P x) : inhabited A :=
inhabited_of_nonempty (obtain w Hw, from H, nonempty.intro w)

/- the Hilbert epsilon function -/

noncomputable definition epsilon {A : Type} [H : nonempty A] (P : A → Prop) : A :=
let u : {x | (∃y, P y) → P x} :=
  strong_indefinite_description P H in
elt_of u

theorem epsilon_spec_aux {A : Type} (H : nonempty A) (P : A → Prop) (Hex : ∃y, P y) :
    P (@epsilon A H P) :=
let u : {x | (∃y, P y) → P x} :=
  strong_indefinite_description P H in
have aux : (∃y, P y) → P (elt_of (strong_indefinite_description P H)), from has_property u,
aux Hex

theorem epsilon_spec {A : Type} {P : A → Prop} (Hex : ∃y, P y) :
    P (@epsilon A (nonempty_of_exists Hex) P) :=
epsilon_spec_aux (nonempty_of_exists Hex) P Hex

theorem epsilon_singleton {A : Type} (a : A) : @epsilon A (nonempty.intro a) (λx, x = a) = a :=
epsilon_spec (exists.intro a (eq.refl a))

noncomputable definition some {A : Type} {P : A → Prop} (H : ∃x, P x) : A :=
@epsilon A (nonempty_of_exists H) P

theorem some_spec {A : Type} {P : A → Prop} (H : ∃x, P x) : P (some H) :=
epsilon_spec H

/- the axiom of choice -/

theorem axiom_of_choice {A : Type} {B : A → Type} {R : Πx, B x → Prop} (H : ∀x, ∃y, R x y) :
  ∃f, ∀x, R x (f x) :=
have H : ∀x, R x (some (H x)), from take x, some_spec (H x),
exists.intro _ H

theorem skolem {A : Type} {B : A → Type} {P : Πx, B x → Prop} :
  (∀x, ∃y, P x y) ↔ ∃f, (∀x, P x (f x)) :=
iff.intro
  (assume H : (∀x, ∃y, P x y), axiom_of_choice H)
  (assume H : (∃f, (∀x, P x (f x))),
    take x, obtain (fw : ∀x, B x) (Hw : ∀x, P x (fw x)), from H,
      exists.intro (fw x) (Hw x))
