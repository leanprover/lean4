import algebra.ring
constants (A : Type.{1}) (A_cr : comm_ring A) (x y z w : A)
attribute A_cr [instance]

open tactic
open simplifier.unit simplifier.ac simplifier.distrib

example : (x + y) * (z + w) = x * z + x * w + y * z + y * w * 1 + 0 :=
by simp >> trace_state >> triv
