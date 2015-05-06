/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.set.map
Author: Jeremy Avigad, Andrew Zipperer

Functions between subsets of finite types, bundled with the domain and range.
-/
import data.set.function
open eq.ops set

record map {X Y : Type} (a : set X) (b : set Y) := (func : X → Y) (mapsto : maps_to func a b)
attribute map.func [coercion]

namespace map

variables {X Y Z: Type}
variables {a : set X} {b : set Y} {c : set Z}

/- the equivalence relation -/

protected definition equiv [reducible] (f1 f2 : map a b) : Prop := eq_on f1 f2 a

namespace equiv_notation
  infix `~` := map.equiv
end equiv_notation
open equiv_notation

protected theorem equiv.refl (f : map a b) : f ~ f := take x, assume H, rfl

protected theorem equiv.symm {f₁ f₂ : map a b} : f₁ ~ f₂ → f₂ ~ f₁ :=
assume H : f₁ ~ f₂,
take x, assume Ha : x ∈ a, eq.symm (H Ha)

protected theorem equiv.trans {f₁ f₂ f₃ : map a b} : f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃ :=
assume H₁ : f₁ ~ f₂, assume H₂ : f₂ ~ f₃,
take x, assume Ha : x ∈ a, eq.trans (H₁ Ha) (H₂ Ha)

protected theorem equiv.is_equivalence {X Y : Type} (a : set X) (b : set Y) :
  equivalence (@equiv X Y a b) :=
mk_equivalence (@equiv X Y a b) (@equiv.refl X Y a b) (@equiv.symm X Y a b) (@equiv.trans X Y a b)

/- compose -/

definition compose (g : map b c) (f : map a b) : map a c :=
map.mk (#function g ∘ f) (maps_to_compose (mapsto g) (mapsto f))

notation g ∘ f := compose g f

/- range -/

definition range (f : map a b) : set Y := image f a

theorem range_eq_range_of_equiv {f1 f2 : map a b} (H : f1 ~ f2) : range f1 = range f2 :=
image_eq_image_of_eq_on H

/- injective -/

definition injective (f : map a b) : Prop := inj_on f a

theorem injective_of_equiv {f1 f2 : map a b} (H1 : f1 ~ f2) (H2 : injective f1) :
  injective f2 :=
inj_on_of_eq_on H1 H2

theorem injective_compose {g : map b c} {f : map a b} (Hg : injective g) (Hf: injective f) :
  injective (g ∘ f) :=
inj_on_compose (mapsto f) Hg Hf

/- surjective -/

definition surjective (f : map a b) : Prop := surj_on f a b

theorem surjective_of_equiv {f1 f2 : map a b} (H1 : f1 ~ f2) (H2 : surjective f1) :
  surjective f2 :=
surj_on_of_eq_on H1 H2

theorem surjective_compose {g : map b c} {f : map a b} (Hg : surjective g) (Hf: surjective f) :
  surjective (g ∘ f) :=
surj_on_compose Hg Hf

/- bijective -/

definition bijective (f : map a b) : Prop := injective f ∧ surjective f

theorem bijective_of_equiv {f1 f2 : map a b} (H1 : f1 ~ f2) (H2 : bijective f1) :
  bijective f2 :=
and.intro (injective_of_equiv H1 (and.left H2)) (surjective_of_equiv H1 (and.right H2))

theorem bijective_compose {g : map b c} {f : map a b} (Hg : bijective g) (Hf: bijective f) :
  bijective (g ∘ f) :=
obtain Hg₁ Hg₂, from Hg,
obtain Hf₁ Hf₂, from Hf,
and.intro (injective_compose Hg₁ Hf₁) (surjective_compose Hg₂ Hf₂)

/- left inverse -/

-- g is a left inverse to f
definition left_inverse (g : map b a) (f : map a b) : Prop := left_inv_on g f a

theorem left_inverse_of_equiv_left {g1 g2 : map b a} {f : map a b} (eqg : g1 ~ g2)
  (H : left_inverse g1 f) : left_inverse g2 f :=
left_inv_on_of_eq_on_left (mapsto f) eqg H

theorem left_inverse_of_equiv_right {g : map b a} {f1 f2 : map a b} (eqf : f1 ~ f2)
  (H : left_inverse g f1) : left_inverse g f2 :=
left_inv_on_of_eq_on_right eqf H

theorem injective_of_left_inverse {g : map b a} {f : map a b} (H : left_inverse g f) :
  injective f :=
inj_on_of_left_inv_on H

theorem left_inverse_compose {f' : map b a} {g' : map c b} {g : map b c} {f : map a b}
    (Hf : left_inverse f' f) (Hg : left_inverse g' g) : left_inverse (f' ∘ g') (g ∘ f) :=
left_inv_on_compose (mapsto f) Hf Hg

/- right inverse -/

-- g is a right inverse to f
definition right_inverse (g : map b a) (f : map a b) : Prop := left_inverse f g

theorem right_inverse_of_equiv_left {g1 g2 : map b a} {f : map a b} (eqg : g1 ~ g2)
  (H : right_inverse g1 f) : right_inverse g2 f :=
left_inverse_of_equiv_right eqg H

theorem right_inverse_of_equiv_right {g : map b a} {f1 f2 : map a b} (eqf : f1 ~ f2)
  (H : right_inverse g f1) : right_inverse g f2 :=
left_inverse_of_equiv_left eqf H

theorem surjective_of_right_inverse {g : map b a} {f : map a b} (H : right_inverse g f) :
  surjective f :=
surj_on_of_right_inv_on (mapsto g) H

theorem right_inverse_compose {f' : map b a} {g' : map c b} {g : map b c} {f : map a b}
    (Hf : right_inverse f' f) (Hg : right_inverse g' g) : right_inverse (f' ∘ g') (g ∘ f) :=
left_inverse_compose Hg Hf

theorem equiv_of_left_inverse_of_right_inverse {g1 g2 : map b a} {f : map a b}
  (H1 : left_inverse g1 f) (H2 : right_inverse g2 f) : g1 ~ g2 :=
eq_on_of_left_inv_of_right_inv (mapsto g2) H1 H2

/- inverse -/

-- g is an inverse to f
definition is_inverse (g : map b a) (f : map a b) : Prop := left_inverse g f ∧ right_inverse g f

theorem bijective_of_is_inverse {g : map b a} {f : map a b} (H : is_inverse g f) : bijective f :=
and.intro
  (injective_of_left_inverse (and.left H))
  (surjective_of_right_inverse (and.right H))

end map
