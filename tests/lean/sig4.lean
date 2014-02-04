check proj1 (tuple 10, 20)
eval proj1 (tuple 10, 20)
eval proj2 (tuple 10, 20)
eval proj2 (tuple 10, 20, 30)
eval proj1 1 (tuple 10, 20, 30, 40)
eval proj1 2 (tuple 10, 20, 30, 40)
eval proj2 2 (tuple 10, 20, 30, 40)
definition NZ : Type := sig x : Nat, 1 ≤ x
variable t : NZ
check proj1 t
check proj2 t
variable t2 : Nat # Nat # Nat
check proj2 t2