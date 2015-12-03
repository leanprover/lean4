constant P : nat → Prop

lemma tst₀ [forward] : ∀ x, P x := -- Fine
sorry

lemma tst₁ [forward] : ∀ x, (: P x :) := -- Fine
sorry

lemma tst₂ [forward] : ∀ x, P (: x :) := -- Error
sorry

lemma tst₃ [forward] : ∀ x, P (: id x :) :=
sorry

reveal tst₀ tst₁ tst₃
print tst₀
print tst₁
print tst₃

definition tst₄ [forward] : ∀ x : nat, (: id x :) = x :=
λ x, rfl
