/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
open decidable

set_option structure.proj_mk_thm true

structure subtype {A : Type} (P : A → Prop) :=
tag :: (elt_of : A) (has_property : P elt_of)

notation `{` binders `|` r:(scoped:1 P, subtype P) `}` := r

definition ex_of_sub {A : Type} {P : A → Prop} : { x | P x } → ∃ x, P x
| (subtype.tag a h) := exists.intro a h

namespace subtype
  variables {A : Type} {P : A → Prop}

  theorem tag_irrelevant {a : A} (H1 H2 : P a) : tag a H1 = tag a H2 :=
  rfl

  theorem tag_eq {a1 a2 : A} {H1 : P a1} {H2 : P a2} (H3 : a1 = a2) : tag a1 H1 = tag a2 H2 :=
  eq.subst H3 (tag_irrelevant H1) H2

  protected theorem eq : ∀ {a1 a2 : {x | P x}} (H : elt_of a1 = elt_of a2), a1 = a2
  | (tag x1 H1) (tag x2 H2) := tag_eq

  protected definition is_inhabited [instance] {a : A} (H : P a) : inhabited {x | P x} :=
  inhabited.mk (tag a H)

  protected definition has_decidable_eq [instance] [H : decidable_eq A] : ∀ s₁ s₂ : {x | P x}, decidable (s₁ = s₂)
  | (tag v₁ p₁) (tag v₂ p₂) :=
  decidable_of_decidable_of_iff (H v₁ v₂)
    (iff.intro tag_eq (λh, subtype.no_confusion h (λa b, a)))
end subtype
