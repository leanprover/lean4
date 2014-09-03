import data.nat data.prod
open nat prod

variable R : nat → nat → Prop
variable f (a b : nat) (H : R a b) : nat
axiom Rtrue (a b : nat) : R a b


check f 1 0 (Rtrue (pr1 (pair 1 0)) 0)
