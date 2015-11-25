-- Basic (propositional) forward chaining with conjunctive conclusions
constants (A B C D E : Prop)
set_option blast.recursor false

definition lemma1 : B → (A → (¬ B) ∧ C) → ¬ A := by blast
definition lemma2 : ¬ B → (A → B ∧ C) → ¬ A := by blast
definition lemma3 : B → (A → C ∧ (¬ B)) → ¬ A := by blast
definition lemma4 : ¬ B → (A → C ∧ B) → ¬ A := by blast
definition lemma5 : B → (A → (¬ B) ∧ E ∧ C) → ¬ A := by blast
definition lemma6 : ¬ B → (A → E ∧ B ∧ C) → ¬ A := by blast
definition lemma7 : B → (A → E ∧ C ∧ (¬ B)) → ¬ A := by blast
definition lemma8 : ¬ B → (A → C ∧ B ∧ E) → ¬ A := by blast
