inductive ValueEffect (V : Type) (R : Type → Type) : Type
| Value : V → ValueEffect
| Effect : R (ValueEffect) → ValueEffect
