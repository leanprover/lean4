-- Testing the unit pre-processor

open simplifier.unit_simp
set_option simplify.max_steps 10000
variables {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Prop}
variables {A B C D E F G : Prop}
variables {X : Type.{1}}

example (H : A ∨ B → E) (nE : ¬ E) : ¬ A ∧ ¬ B := by blast
example (H : A ∨ B → E) (nE : ¬ E) : ¬ A ∧ ¬ B := by blast
example (H : A ∨ B → E ∧ F) (nE : ¬ E) : ¬ A ∧ ¬ B := by blast
example (H : A ∨ (B ∧ C) → E ∧ F) (c : C) (nE : ¬ E) : ¬ A ∧ ¬ B := by blast
example (H : A ∨ (B ∧ C) → (G → E ∧ F)) (g : G) (c : C) (nE : ¬ E) : ¬ A ∧ ¬ B := by blast
