-- Basic (propositional) forward chaining with clauses
constants (A B C D E : Prop)
set_option blast.recursor false

definition lemma1 : A → (A ∨ B → C) → C := by blast
definition lemma2 : B → (A ∨ B → C) → C := by blast
definition lemma3 : A → B → (A → B ∨ C → D) → D := by blast
definition lemma4 : A → B → (A → B ∨ C ∨ C → D) → D := by blast
definition lemma5 : A → B → (E ∨ A ∨ E → E ∨ B ∨ C ∨ C → D) → D := by blast
definition lemma6 : A → (A → B → C) → ¬ C → ¬ B := by blast
definition lemma7 : ¬ D → B → (A → E ∨ B ∨ C ∨ C → D) → ¬ A := by blast
definition lemma8 : ¬ D → B → (A ∨ E → E ∨ B ∨ C ∨ C → D) → ¬ (A ∨ E) := by blast
