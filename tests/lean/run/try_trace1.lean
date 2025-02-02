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
