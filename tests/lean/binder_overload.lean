import data.set data.finset
open nat set finset

constant S : set nat
constant s : finset nat

check {x ∈ S | x > 0}
check {x ∈ s | x > 0}
set_option pp.all true
check {x ∈ S | x > 0}
check {x ∈ s | x > 0}
