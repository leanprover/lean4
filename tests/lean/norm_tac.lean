import Int
import tactic
set::option pp::implicit true
set::option pp::coercion true
set::option pp::notation false
variable vector (A : Type) (sz : Nat) : Type
variable read {A : Type} {sz : Nat} (v : vector A sz) (i : Nat) (H : i < sz) : A
variable V1 : vector Int 10
definition D := read V1 1 (by trivial)
print environment 1
variable b : Bool
definition a := b
theorem T : b => a := (by (* imp_tac() .. normalize_tac() .. assumption_tac() *))
