universe variables u
variables {α : Type u}
variables [comm_ring α]
open tactic

example (x1 x2 x3 x4 x5 x6 : α) : x1*x4 = x1 → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 → x1 = x1*(x6*x3) :=
by cc

example (y1 y2 x2 x3 x4 x5 x6 : α) : (y1 + y2)*x4 = (y2 + y1) → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 → (y2 + y1) = (y1 + y2)*(x6*x3) :=
by cc
