import data.set
open set function eq.ops

variables {X Y Z : Type}

lemma image_compose (f : Y → X) (g : X → Y) (a : set X) : (f ∘ g) ' a = f ' (g ' a) :=
ext (take z,
  iff.intro
    (assume Hz : z ∈ (f ∘ g) ' a,
      obtain x (Hx₁ : x ∈ a) (Hx₂ : f (g x) = z), from Hz,
      have Hgx : g x ∈ g ' a, from mem_image Hx₁ rfl,
      show z ∈ f ' (g ' a), from mem_image Hgx Hx₂)
    (assume Hz : z ∈ f ' (g ' a),
      obtain y [x (Hz₁ : x ∈ a) (Hz₂ : g x = y)] (Hy₂ : f y = z), from Hz,
      show z ∈ (f ∘ g) ' a, from mem_image Hz₁ (Hz₂⁻¹ ▸ Hy₂)))
