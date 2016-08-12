import data.finset data.set
open finset set

attribute [coercion]
definition to_set {A : Type} (s : finset A) : set A := λ a, a ∈ s

constant P {A : Type} (s : set A) : Prop

variable s : finset nat

check P s
