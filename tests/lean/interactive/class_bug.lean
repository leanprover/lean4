import data.nat.basic
open nonempty inhabited nat classical

attribute [instance]
theorem int_inhabited : inhabited nat := inhabited.mk zero

check epsilon (λ x : nat, true)
