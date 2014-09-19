import data.int
open int

protected theorem has_decidable_eq [instance] : decidable_eq ℤ :=
take (a b : ℤ), _

variable n : nat
variable i : int
check n + i
