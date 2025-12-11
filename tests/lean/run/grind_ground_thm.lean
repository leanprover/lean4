opaque π : Rat
axiom pi_pos : 0 < π

theorem two_pi_pos : 0 < 2 * π := by
  grind [pi_pos]

/--
info: Try these:
  [apply] grind only [pi_pos]
  [apply] grind =>
    instantiate only [pi_pos]
    linarith
-/
#guard_msgs in
theorem two_pi_pos' : 0 < 2 * π := by
  grind? [pi_pos]

attribute [grind .] pi_pos

theorem two_pi_pos'' : 0 < 2 * π := by
  grind

/--
info: Try these:
  [apply] grind only [pi_pos]
  [apply] grind =>
    instantiate only [pi_pos]
    linarith
-/
#guard_msgs in
theorem two_pi_pos''' : 0 < 2 * π := by
  grind?

def f (x : Nat) := x

-- Should not instantiate/activate pi_pos
/--
trace: [grind.ematch] activated `f.eq_1`, [f #0]
[grind.ematch.instance] f.eq_1: f x = x
-/
#guard_msgs (drop error, trace) in
example : 1 < x → 2 < f x := by
  set_option trace.grind.ematch true in
  set_option trace.grind.ematch.instance true in
  grind [f]

-- Should instantiate/activate pi_pos
/-- trace: [grind.ematch] activated `pi_pos`, [@LT.lt `[Rat] `[Rat.instLT] `[0] `[π]] -/
#guard_msgs in
example : π < x → 0 < x := by
  set_option trace.grind.ematch true in
  grind
