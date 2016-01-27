constants (P : ℕ → Prop) (R : Prop)
lemma foo [intro!] : (: P 0 :) →  R := sorry
constants (P0 : P 0)
attribute P0 [intro!]
example : R :=
by grind -- fails
