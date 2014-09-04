-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad

import logic.classes.inhabited logic.core.eq logic.classes.decidable

open decidable

inductive subtype {A : Type} (P : A → Prop) : Type :=
tag : Πx : A, P x → subtype P

notation `{` binders `,` r:(scoped P, subtype P) `}` := r

namespace subtype

section
  parameter {A : Type}
  parameter {P : A → Prop}

  -- TODO: make this a coercion?
  definition  elt_of (a : {x, P x}) : A := rec (λ x y, x) a
  theorem has_property (a : {x, P x}) : P (elt_of a) := rec (λ x y, y) a

  theorem elt_of_tag (a : A) (H : P a) : elt_of (tag a H) = a := refl a

  theorem destruct [protected] {Q : {x, P x} → Prop} (a : {x, P x})
      (H : ∀(x : A) (H1 : P x), Q (tag x H1)) : Q a :=
    rec H a

  theorem tag_irrelevant {a : A} (H1 H2 : P a) : tag a H1 = tag a H2 :=
  rfl

  theorem tag_elt_of (a : subtype P) : ∀(H : P (elt_of a)), tag (elt_of a) H = a :=
    destruct a (take (x : A) (H1 : P x) (H2 : P x), rfl)

  theorem tag_eq {a1 a2 : A} {H1 : P a1} {H2 : P a2} (H3 : a1 = a2) : tag a1 H1 = tag a2 H2 :=
  subst H3 (take H2, tag_irrelevant H1 H2) H2

  theorem subtype_eq {a1 a2 : {x, P x}} : ∀(H : elt_of a1 = elt_of a2), a1 = a2 :=
  destruct a1 (take x1 H1, destruct a2 (take x2 H2 H, tag_eq H))

  theorem subtype_inhabited [instance] {a : A} (H : P a) : inhabited {x, P x} :=
  inhabited_mk (tag a H)

  theorem eq_decidable [protected] [instance] (a1 a2 : {x, P x})
    (H : decidable (elt_of a1 = elt_of a2)) : decidable (a1 = a2) :=
  have H1 : (a1 = a2) ↔ (elt_of a1 = elt_of a2), from
    iff_intro (assume H, subst H rfl) (assume H, subtype_eq H),
  decidable_iff_equiv _ (iff_symm H1)

end

end subtype
