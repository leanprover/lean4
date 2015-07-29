import logic.choice data.nat.basic
open nonempty inhabited nat

theorem int_inhabited [instance] : inhabited nat := inhabited.mk zero

check epsilon (λ x : nat, true)
