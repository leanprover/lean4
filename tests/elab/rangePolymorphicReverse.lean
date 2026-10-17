import Std.Data.Iterators

/-! Tests reverse iteration over every polymorphic range shape. -/

/-- info: [4, 3, 2, 1] -/
#guard_msgs in
#eval (1...=4).revToList

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval (1...4).revToList

/-- info: [4, 3, 2] -/
#guard_msgs in
#eval (1<...=4).revToList

/-- info: [3, 2] -/
#guard_msgs in
#eval (1<...4).revToList

/-- info: [4, 3, 2, 1, 0] -/
#guard_msgs in
#eval (*...=4).revToList

/-- info: [3, 2, 1, 0] -/
#guard_msgs in
#eval (*...4).revToList

/-- info: [2, 1, 0, -1, -2] -/
#guard_msgs in
#eval ((-2 : Int) ...=2).revToList

/-- info: [1, 0, -1] -/
#guard_msgs in
#eval ((-2 : Int) <...2).revToList

/-- info: [4, 3, 2] -/
#guard_msgs in
#eval ((2 : Fin 5) ...*).revToList

/-- info: [4, 3] -/
#guard_msgs in
#eval ((2 : Fin 5) <...*).revToList

/-- info: [4, 3, 2, 1, 0] -/
#guard_msgs in
#eval ((*...*).revToList : List (Fin 5))
