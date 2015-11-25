-- Basic (propositional) forward chaining with disjunctive antecedents and conjunctive conclusions
constants (A B C D E F : Prop)
set_option blast.recursor false

definition lemma1 : B → (A ∨ E → (¬ B) ∧ C) → ¬ (A ∨ E) := by blast
definition lemma2 : ¬ B → (A ∨ E → B ∧ C) → ¬ (A ∨ E) := by blast
definition lemma3 : A → ¬ D → (A ∨ E → B → C ∧ D) → ¬ B := by blast
definition lemma4 : A → ¬ E → (A → B → E ∧ F) → ¬ B := by blast
definition lemma5 : (A → B) → ¬ B → ¬ A := by blast
definition lemma6 : (A → B ∧ C) → ¬ B → ¬ A := by blast
