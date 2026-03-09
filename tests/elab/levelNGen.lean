opaque test1 {α : Sort _} : α → Sort u_1
/-- info: test1.{u_1, u_2} {α : Sort u_2} : α → Sort u_1 -/
#guard_msgs in
#check test1

def test2 {α : Sort _} : α → Sort u_1 := sorry
/-- info: test2.{u_1, u_2} {α : Sort u_2} : α → Sort u_1 -/
#guard_msgs in
#check test2

variable {α : Sort _} in def test3 : α → Sort _ := sorry
/-- info: test3.{u_1, u_2} {α : Sort u_1} : α → Sort u_2 -/
#guard_msgs in
#check test3
