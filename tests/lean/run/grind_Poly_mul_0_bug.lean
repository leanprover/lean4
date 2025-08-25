module
open Int.Linear

def p : Poly := .add 1 1 <| .add 2 0 <| .num 3

/-- info: Int.Linear.Poly.num 0 -/
#guard_msgs (info) in
#eval p |>.mul 0
