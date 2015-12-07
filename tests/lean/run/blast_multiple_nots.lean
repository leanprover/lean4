constants a b c d : Prop

set_option blast.strategy "unit"

example (H : ¬ a → ¬ b → ¬ c ∨ ¬ d) : ¬ a → c → d → ¬ b → false :=
by blast

set_option blast.strategy "preprocess"

example : ¬¬¬¬¬a → ¬¬a → false :=
by blast

example : ¬¬¬¬¬a → ¬¬¬¬a → false :=
by blast

example : ¬¬¬¬¬a → a → false :=
by blast

example : ¬¬a → ¬¬¬¬¬a → false :=
by blast

example : ¬¬¬¬¬a → ¬¬¬¬¬¬¬¬a → false :=
by blast

example : ¬¬¬¬¬a → a → false :=
by blast

example : ¬¬¬¬¬¬¬¬a → ¬¬¬¬¬a → false :=
by blast
