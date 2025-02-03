set_option grind.warning false

/-- info: Try this: simp -/
#guard_msgs (info) in
example : [1, 2] ≠ [] := by
  try?

/-- info: Try this: simp +arith -/
#guard_msgs (info) in
example : 4 + x + y ≥ 1 + x  := by
  try?

/-- info: Try this: grind? -/
#guard_msgs (info) in
example (f : Nat → Nat) : f a = b → a = c → f c = b := by
  try?

def f : Nat → Nat
  | 0 => 1
  | _ => 2

/-- info: Try this: grind? [= f] -/
#guard_msgs (info) in
example : f (f 0) > 0 := by
  try?

/-- info: Try this: grind? [= f.eq_def] -/
#guard_msgs (info) in
example : f x > 0 := by
  try?

def app : List α → List α → List α
  | [], bs => bs
  | a::as, bs => a :: app as bs

/-- info: Try this: grind? [= app] -/
#guard_msgs (info) in
example : app [a, b] [c] = [a, b, c] := by
  try?

/-- info: Try this: (induction as, bs using app.induct) <;> grind? [= app] -/
#guard_msgs (info) in
example : app (app as bs) cs = app as (app bs cs) := by
  try?
