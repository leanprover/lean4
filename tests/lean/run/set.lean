import logic
open bool nat

definition set (T : Type) := T → bool
definition mem {A : Type} (x : A) (s : set A) := s x
infix ` ∈ ` := mem

check 1 ∈ (λ x : nat, tt)
