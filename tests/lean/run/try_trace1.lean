set_option grind.warning false

/--
info: Try these:
• simp
• simp only [ne_eq, reduceCtorEq, not_false_eq_true]
• grind
• grind only
-/
#guard_msgs (info) in
example : [1, 2] ≠ [] := by
  try?

/--
info: Try these:
• simp +arith
• simp +arith only [ge_iff_le]
• grind
• grind only
-/
#guard_msgs (info) in
example : 4 + x + y ≥ 1 + x  := by
  try?

/--
info: Try these:
• grind
• grind only
-/
#guard_msgs (info) in
example (f : Nat → Nat) : f a = b → a = c → f c = b := by
  try?

def f : Nat → Nat
  | 0 => 1
  | _ => 2

/--
info: Try these:
• grind [= f]
• grind only [f]
-/
#guard_msgs (info) in
example : f (f 0) > 0 := by
  try?

/--
info: Try these:
• grind [= f.eq_def]
• grind only [= f.eq_def]
-/
#guard_msgs (info) in
example : f x > 0 := by
  try?

def app : List α → List α → List α
  | [], bs => bs
  | a::as, bs => a :: app as bs

/--
info: Try these:
• rfl
• grind [= app]
• grind only [app]
-/
#guard_msgs (info) in
example : app [a, b] [c] = [a, b, c] := by
  try?

/--
info: Try these:
• (induction as, bs using app.induct) <;> grind [= app]
• (induction as, bs using app.induct) <;> grind only [app]
-/
#guard_msgs (info) in
example : app (app as bs) cs = app as (app bs cs) := by
  try?
