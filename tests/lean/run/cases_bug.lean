import logic.cast

theorem cast_heq₂ : ∀ {A B : Type} (H : A = B) (a : A), cast H a == a
| A A (eq.refl A) a := heq_of_eq !cast_eq
