syntax "#" noWs hexnum : term
open Lean in
macro_rules
  | `(#$n:hexnum) => `(($(quote n.getHexNumSize), $(quote n.getHexNumVal)))

/-- info: (4, 44733) : Nat × Nat -/
#guard_msgs in
#check #aebd

/-- info: (1, 10) : Nat × Nat -/
#guard_msgs in
#check #a

/-- info: (2, 16) : Nat × Nat -/
#guard_msgs in
#check #10

/-- info: (2, 5) : Nat × Nat -/
#guard_msgs in
#check #05

/-- info: (3, 10) : Nat × Nat -/
#guard_msgs in
#check #00a

/-- info: (8, 65536) : Nat × Nat -/
#guard_msgs in
#check #0001_0000
