class P (n : Nat)
class Q (n : Nat)
variable [∀ (n : Nat) [P n], Q n]
example [P 7] : Q 7 := inferInstance
