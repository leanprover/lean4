check sig x : Nat, x > 0
check tuple 10, 20
check tuple 10, true
check tuple true, 20
check tuple (Bool # Nat) : true, 20
check tuple true, true
check tuple Bool ⨯ Bool : true, true
variable a : Nat
axiom Ha : 1 ≤ a
definition NZ : Type := sig x : Nat, 1 ≤ x
check NZ
check tuple NZ : a, Ha
check tuple Nat # Nat : true, 20
check tuple Bool # Bool : true, 20
