/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Andrew Zipperer

Functions between subsets of finite types, bundled with the domain and range.
-/
import data.set.function
open eq.ops

namespace set

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
  equivalence (@map.equiv X Y a b) :=
mk_equivalence (@map.equiv X Y a b) (@equiv.refl X Y a b) (@equiv.symm X Y a b)
    (@equiv.trans X Y a b)

/- compose -/

protected definition compose (g : map b c) (f : map a b) : map a c :=
map.mk (#function g ∘ f) (maps_to_compose (mapsto g) (mapsto f))

notation g ∘ f := map.compose g f

/- range -/

protected definition range (f : map a b) : set Y := image f a

theorem range_eq_range_of_equiv {f1 f2 : map a b} (H : f1 ~ f2) : map.range f1 = map.range f2 :=
image_eq_image_of_eq_on H

/- injective -/

protected definition injective (f : map a b) : Prop := inj_on f a

theorem injective_of_equiv {f1 f2 : map a b} (H1 : f1 ~ f2) (H2 : map.injective f1) :
  map.injective f2 :=
inj_on_of_eq_on H1 H2

theorem injective_compose {g : map b c} {f : map a b} (Hg : map.injective g) (Hf: map.injective f) :
  map.injective (g ∘ f) :=
inj_on_compose (mapsto f) Hg Hf

/- surjective -/

protected definition surjective (f : map a b) : Prop := surj_on f a b

theorem surjective_of_equiv {f1 f2 : map a b} (H1 : f1 ~ f2) (H2 : map.surjective f1) :
  map.surjective f2 :=
surj_on_of_eq_on H1 H2

theorem surjective_compose {g : map b c} {f : map a b} (Hg : map.surjective g)
    (Hf: map.surjective f) :
  map.surjective (g ∘ f) :=
surj_on_compose Hg Hf

theorem image_eq_of_surjective {f : map a b} (H : map.surjective f) : f ' a = b :=
image_eq_of_maps_to_of_surj_on (map.mapsto f) H

/- bijective -/

protected definition bijective (f : map a b) : Prop := map.injective f ∧ map.surjective f

theorem bijective_of_equiv {f1 f2 : map a b} (H1 : f1 ~ f2) (H2 : map.bijective f1) :
  map.bijective f2 :=
and.intro (injective_of_equiv H1 (and.left H2)) (surjective_of_equiv H1 (and.right H2))

theorem bijective_compose {g : map b c} {f : map a b} (Hg : map.bijective g) (Hf: map.bijective f) :
  map.bijective (g ∘ f) :=
obtain Hg₁ Hg₂, from Hg,
obtain Hf₁ Hf₂, from Hf,
and.intro (injective_compose Hg₁ Hf₁) (surjective_compose Hg₂ Hf₂)

theorem image_eq_of_bijective {f : map a b} (H : map.bijective f) : f ' a = b :=
image_eq_of_surjective (proof and.right H qed)

/- left inverse -/

-- g is a left inverse to f
protected definition left_inverse (g : map b a) (f : map a b) : Prop := left_inv_on g f a

theorem left_inverse_of_equiv_left {g1 g2 : map b a} {f : map a b} (eqg : g1 ~ g2)
  (H : map.left_inverse g1 f) : map.left_inverse g2 f :=
left_inv_on_of_eq_on_left (mapsto f) eqg H

theorem left_inverse_of_equiv_right {g : map b a} {f1 f2 : map a b} (eqf : f1 ~ f2)
  (H : map.left_inverse g f1) : map.left_inverse g f2 :=
left_inv_on_of_eq_on_right eqf H

theorem injective_of_left_inverse {g : map b a} {f : map a b} (H : map.left_inverse g f) :
  map.injective f :=
inj_on_of_left_inv_on H

theorem left_inverse_compose {f' : map b a} {g' : map c b} {g : map b c} {f : map a b}
    (Hf : map.left_inverse f' f) (Hg : map.left_inverse g' g) :
  map.left_inverse (f' ∘ g') (g ∘ f) :=
left_inv_on_compose (mapsto f) Hf Hg

/- right inverse -/

-- g is a right inverse to f
protected definition right_inverse (g : map b a) (f : map a b) : Prop := map.left_inverse f g

theorem right_inverse_of_equiv_left {g1 g2 : map b a} {f : map a b} (eqg : g1 ~ g2)
  (H : map.right_inverse g1 f) : map.right_inverse g2 f :=
map.left_inverse_of_equiv_right eqg H

theorem right_inverse_of_equiv_right {g : map b a} {f1 f2 : map a b} (eqf : f1 ~ f2)
  (H : map.right_inverse g f1) : map.right_inverse g f2 :=
map.left_inverse_of_equiv_left eqf H

theorem right_inverse_of_injective_of_left_inverse {f : map a b} {g : map b a}
    (injf : map.injective f) (lfg : map.left_inverse f g) :
  map.right_inverse f g :=
right_inv_on_of_inj_on_of_left_inv_on (mapsto f) (mapsto g) injf lfg

theorem surjective_of_right_inverse {g : map b a} {f : map a b} (H : map.right_inverse g f) :
  map.surjective f :=
surj_on_of_right_inv_on (mapsto g) H

theorem left_inverse_of_surjective_of_right_inverse {f : map a b} {g : map b a}
    (surjf : map.surjective f) (rfg : map.right_inverse f g) :
  map.left_inverse f g :=
left_inv_on_of_surj_on_right_inv_on surjf rfg

theorem right_inverse_compose {f' : map b a} {g' : map c b} {g : map b c} {f : map a b}
    (Hf : map.right_inverse f' f) (Hg : map.right_inverse g' g) :
  map.right_inverse (f' ∘ g') (g ∘ f) :=
map.left_inverse_compose Hg Hf

theorem equiv_of_map.left_inverse_of_right_inverse {g1 g2 : map b a} {f : map a b}
  (H1 : map.left_inverse g1 f) (H2 : map.right_inverse g2 f) : g1 ~ g2 :=
eq_on_of_left_inv_of_right_inv (mapsto g2) H1 H2

/- inverse -/

-- g is an inverse to f
protected definition is_inverse (g : map b a) (f : map a b) : Prop :=
map.left_inverse g f ∧ map.right_inverse g f

theorem bijective_of_is_inverse {g : map b a} {f : map a b} (H : map.is_inverse g f) :
  map.bijective f :=
and.intro
  (injective_of_left_inverse (and.left H))
  (surjective_of_right_inverse (and.right H))

end map
end set
