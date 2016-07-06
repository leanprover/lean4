import algebra.ring
open tactic

constants (A : Type.{1}) (x y z w : A) (f : A → A) (H₁ : f (f x) = f y) (H₂ : f (f y) = f z) (H₃ : f (f z) = w)

definition foo : f (f (f (f x))) = w :=
by do h₁ ← mk_const "H₁",
      h₂ ← mk_const "H₂",
      h₃ ← mk_const "H₃",
      simp_core [h₁, h₂, h₃] triv,
      triv

print foo
