import data.int
open int

theorem has_decidable_eq [instance] [protected] : decidable_eq ℤ :=
decidable_eq.intro (λ (a b : ℤ), _)

variable n : nat
variable i : int
check n + i
