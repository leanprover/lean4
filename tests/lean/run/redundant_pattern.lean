constants P : nat → Prop
constants R : nat → nat → Prop
constants f g : nat → nat

definition foo [forward] (m n k : nat) : P (f m) → P (g n) → P (f k) → P k ∧ R (g m) (f n) ∧ P (g m) ∧ P (f n) :=
sorry

print foo
