import logic.cast

theorem cast_heq : ∀ {A B : Type} (H : A = B) (a : A), cast H a == a
| A A (eq.refl A) a := heq.of_eq (cast_refl a)
