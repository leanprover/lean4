import data.fintype
open function

section test
variable {A : Type}
variable [finA : fintype A]
include finA
variable [deceqA : decidable_eq A]
include deceqA

example : decidable_pred (@injective A A) :=
_

example : decidable_pred (@surjective A A) :=
_

end test
