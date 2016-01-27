constants (P : ℕ → Prop) (Q : Prop)
lemma foo [intro!] [forward] : (: P 0 :) → Q := sorry
example : P 0 → Q :=
by grind
