constant P : nat → Prop

lemma tst₁ [forward] : ∀ x, (: P x :) := -- Fine
sorry

lemma tst₂ [forward] : ∀ x, P (: x :) := -- Error
sorry
