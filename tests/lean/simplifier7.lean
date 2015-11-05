-- Simplifying the operator with a user-defined congruence
import logic.connectives

constants (P1 Q1 P2 Q2 P3 Q3 : Prop) (H1 : P1 ↔ Q1) (H2 : P2 ↔ Q2) (H3 : P3 ↔ Q3)
constants (f g : Prop → Prop → Prop)
constants (Hf : and = f) (Hg : f = g)

attribute H1 [simp]
attribute H2 [simp]
attribute H3 [simp]
attribute Hf [simp]
attribute Hg [simp]

#simplify iff 2 (and P1 (and P2 P3))
#simplify iff 2 (and P1 (iff P2 P3))
