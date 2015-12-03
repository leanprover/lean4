constants f g : nat → Prop

definition foo₁ [forward] : ∀ x, f x ∧ g x            := sorry
definition foo₂ [forward] : ∀ x, (: f x :) ∧ g x      := sorry
definition foo₃ [forward] : ∀ x, (: f (id x) :) ∧ g x := sorry

print foo₁
print foo₂
print foo₃ -- id is unfolded
