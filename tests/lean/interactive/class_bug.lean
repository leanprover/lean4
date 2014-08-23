import logic.axioms.hilbert data.nat.basic
using nonempty inhabited nat

theorem int_inhabited [instance] : inhabited nat := inhabited_mk zero

check epsilon (λ x : nat, true)
