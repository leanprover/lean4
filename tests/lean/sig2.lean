check sig x : Nat, x > 0
check tuple 10, 20, (Nat # Nat)
check tuple 10, true, (Nat # Nat)
check tuple true, 20, (Nat # Nat)
check tuple true, 20, (Bool # Nat)
check tuple true, true, (Bool # Bool)
check tuple true, true, (Bool ⨯ Bool)
variable a : Nat
axiom Ha : 1 ≤ a
definition NZ : Type := sig x : Nat, 1 ≤ x
check NZ
check tuple a, Ha, NZ
