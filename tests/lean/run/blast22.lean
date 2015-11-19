-- Basic (propositional) forward chaining
constants (A B C D : Prop)

definition lemma1 : A → (A → B) → B := by blast
definition lemma2 : ¬ B → (A → B) → ¬ A := by blast
definition lemma3 : ¬ C → A → (A → B → C) → ¬ B := by blast
definition lemma4 : C → A → (A → B → ¬ C) → ¬ B := by blast
-- TODO(dhs): [forward_action] is responsible for
-- eliminating double negation
definition lemma5 : C → A → (A → ¬ B → ¬ C) → ¬ ¬ B := by blast
definition lemma6 : (A → B → ¬ C) → C → A → ¬ B := by blast
definition lemma7 : ¬ C → (A → B → C) → A → ¬ B := by blast
definition lemma8 : A → (A → B) → C → B ∧ C := by blast
