check sig x : Nat, x > 0
check pair 10 20
check pair 10 true
check pair true 20
check pair true 20 : Bool # Nat
check pair true true
check pair true true : Bool ⨯ Bool
variable a : Nat
axiom Ha : 1 ≤ a
definition NZ : Type := sig x : Nat, 1 ≤ x
check NZ
check pair a Ha : NZ
check pair true 20 : Nat # Nat
check pair true 20 : Bool # Bool
