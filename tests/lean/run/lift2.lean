namespace test
inductive {u₁ u₂} lift (A : Type u₁) : Type (max 1 u₁ u₂)
| inj : A → lift

set_option pp.universes true

variables (A : Type 3) (B : Type 1)
check A = lift.{1 3} B

universe variables u
variables (C : Type (u+2)) (D : Type u)
check C = lift.{u u+2} D
end test
