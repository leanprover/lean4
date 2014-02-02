import Int
import tactic
set_option pp::implicit true
set_option pp::coercion true
set_option pp::notation false
variable vector (A : Type) (sz : Nat) : Type
variable read {A : Type} {sz : Nat} (v : vector A sz) (i : Nat) (H : i < sz) : A
variable V1 : vector Int 10
axiom H : 1 < 10
add_rewrite H
definition D := read V1 1 (by simp)
print environment 1
variable b : Bool
definition a := b
theorem T : b → a := (by (* normalize_tac() .. assumption_tac() *))
