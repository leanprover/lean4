import logic

inductive lift.{l₁ l₂} (A : Type.{l₁}) : Type.{(max 1 l₁ l₂)} :=
inj : A → lift A

set_option pp.universes true

variables (A : Type.{3}) (B : Type.{1})
check A = lift B

universe u
variables (C : Type.{u+2}) (D : Type.{u})
check C = lift D
