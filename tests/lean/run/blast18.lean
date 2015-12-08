-- Backward chaining with tagged rules
set_option blast.strategy "backward"
constants {P Q R S T U : Prop} (Hpq : P → Q) (Hqr : Q → R) (Hrs : R → S) (Hst : S → T)
constants (Huq : U → Q) (Hur : U → R) (Hus : U → S) (Hut : U → T)
attribute Hpq [intro]
attribute Hqr [intro]
attribute Hrs [intro]
attribute Hst [intro]

attribute Huq [intro]
attribute Hur [intro]
attribute Hus [intro]
attribute Hut [intro]

definition lemma1 (p : P) : Q := by blast
definition lemma2 (p : P) : R := by blast
definition lemma3 (p : P) : S := by blast
definition lemma4 (p : P) : T := by blast
