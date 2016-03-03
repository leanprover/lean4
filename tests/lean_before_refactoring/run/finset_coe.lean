import data.finset data.set
open finset set

definition to_set [coercion] {A : Type} (s : finset A) : set A := λ a, a ∈ s

constant P {A : Type} (s : set A) : Prop

variable s : finset nat

check P s
