import algebra.ring
open tactic

constants (A : Type.{1}) (x y z w v : A) (f : A → A) (H₁ : f (f x) = f y) (H₂ : f (f y) = f z) (H₃ : f (f z) = w) (g : A → A → A)
          (H : ∀ a b : A, f (f (f (f a))) = b → f (g a b) = b)

meta_definition my_prove_fn : tactic unit :=
do h₁ ← mk_const "H₁",
      h₂ ← mk_const "H₂",
      h₃ ← mk_const "H₃",
      simp_core [h₁, h₂, h₃] triv,
      triv

set_option trace.simplifier.prove true
example : f (g x w) = w  :=
by do h ← mk_const "H",
      simp_core [h] my_prove_fn,
      triv
