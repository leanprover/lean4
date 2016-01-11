import data.unit
open unit

set_option blast.strategy "cc"
set_option blast.cc.subsingleton true
set_option blast.cc.heq true

example (a b : unit) : a = b :=
by blast

example (a b : nat) (h₁ : a = 0) (h₂ : b = 0) : a = b → h₁ == h₂ :=
by blast

definition inv' : ∀ (a : nat), a ≠ 0 → nat :=
sorry

example (a b : nat) (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a = b → inv' a h₁ = inv' b h₂ :=
by blast
