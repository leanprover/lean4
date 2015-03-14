import algebra.group
open algebra

variable {A : Type}
variable [s : group A]
variable (a : A)

check 1 * 1 * a
set_option pp.notation false
check 1 * a

variable [s2 : add_comm_group A]

set_option pp.notation true

check 0 + a

set_option pp.notation false
check 0 + a
