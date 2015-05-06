import data.set
open set function eq.ops

variables {X Y Z : Type}

lemma image_compose (f : Y → X) (g : X → Y) (a : set X) : (f ∘ g) '[a] = f '[g '[a]] :=
setext (take z,
  iff.intro
    (assume Hz,
      obtain x Hx₁ Hx₂, from Hz,
      by repeat (apply in_image | assumption | reflexivity))
    (assume Hz,
      obtain y [x Hz₁ Hz₂] Hy₂, from Hz,
      by repeat (apply in_image | assumption | esimp [compose] | rewrite Hz₂)))
