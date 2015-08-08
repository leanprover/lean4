import data.set data.finset
open set finset

variables (A : Type) [deceqA : decidable_eq A]
include deceqA
variables s t : finset A

set_option pp.coercions true
set_option pp.notation false
set_option pp.full_names true
check (s ∪ t : set A)
