-- Backward chaining with hypotheses
constants {P Q R S T U : Prop}
constants (Huq : U → Q) (Hur : U → R) (Hus : U → S) (Hut : U → T)
attribute [intro] Huq Hur Hus Hut

open tactic

definition lemma1 : (P → Q) → P → Q := by (intros >> back_chaining_using_hs)
definition lemma2 : (P → Q) → (Q → R) → P → R := by (intros >> back_chaining_using_hs)
definition lemma3 : (P → Q) → (Q → R) → (R → S) → P → S := by (intros >> back_chaining_using_hs)
definition lemma4 : (P → Q) → (Q → R) → (R → S) → (S → T) → P → T := by (intros >> back_chaining_using_hs)
