set_option grind.warning false
%reset_grind_attrs

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

/--
info: Try these:
• · expose_names; induction as, bs_1 using app.induct <;> grind [= app]
• · expose_names; induction as, bs_1 using app.induct <;> grind only [app]
-/
#guard_msgs (info) in
example : app (app as bs) cs = app as (app bs cs) := by
  have bs := 20 -- shadow variable in the goal
  try?

/--
info: Try these:
• · expose_names; induction as, bs using app.induct <;> grind [= app]
• · expose_names; induction as, bs using app.induct <;> grind only [app]
-/
#guard_msgs (info) in
example : app (app as bs) cs = app as (app bs cs) := by
  revert as bs cs
  intro _ _ _
  -- `as`, `bs`, and `cs` now have inaccessible names.
  try?

def concat : List α → α → List α
  | .nil,       b => .cons b .nil
  | .cons a as, b => .cons a (concat as b)

attribute [simp] concat

/--
info: Try this: ·
  induction as, a using concat.induct
  · rfl
  · simp_all
-/
#guard_msgs (info) in
example (as : List α) (a : α) : concat as a = as ++ [a] := by
  try?

def foo : Nat → Nat
  | 0   => 1
  | x+1 => foo x - 1


/--
info: Try this: ·
  induction x using foo.induct
  · grind [= foo]
  · sorry
-/
#guard_msgs (info) in
example : foo x > 0 := by
  try?  -- `try?` does not solve all subgoals.
  sorry
