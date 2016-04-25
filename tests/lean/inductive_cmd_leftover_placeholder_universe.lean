inductive ValueEffect (V : Type) (R : Type → Type) : Type :=
| Value : V → ValueEffect V R
| Effect : R (ValueEffect V R) → ValueEffect V R
