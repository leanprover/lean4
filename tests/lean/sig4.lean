check proj1 (pair 10 20)
eval proj1 (pair 10 20)
eval proj2 (pair 10 20)
eval proj2 (pair 10 (pair 20 30))
eval proj1  (pair 10 (pair 20 30))
eval proj1 (proj2 (pair 10 (pair 20 30)))
eval proj2 (proj2 (proj2 (pair 10 (pair 20 (pair 30 40)))))
definition NZ : Type := sig x : Nat, 1 ≤ x
variable t : NZ
check proj1 t
check proj2 t
variable t2 : Nat # Nat # Nat
check proj2 t2