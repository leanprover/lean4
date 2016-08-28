set_option new_elaborator true

lemma ex4 (A : Type) : ∀ (a b : A) (H : a = b), b = a
| .z z (eq.refl .z) := eq.refl z
