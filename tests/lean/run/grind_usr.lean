opaque f : Nat → Nat

/--
error: the modifier `usr` is only relevant in parameters for `grind only`
-/
#guard_msgs (error) in
@[grind usr]
theorem fthm : f (f x) = f x := sorry

/-- info: [grind.ematch.pattern] fthm: [f #0] -/
#guard_msgs (info) in
set_option trace.grind.ematch.pattern true in
example : f (f (f x)) = f x := by
  grind only [fthm]

/--
info: [grind.ematch.instance] fthm: f (f x) = f x
[grind.ematch.instance] fthm: f (f (f x)) = f (f x)
[grind.ematch.instance] fthm: f (f (f (f x))) = f (f (f x))
-/
#guard_msgs (info) in
set_option trace.grind.ematch.instance true in
example : f (f (f x)) = f x := by
  grind only [fthm]

/--
info: [grind.ematch.instance] fthm: f (f x) = f x
[grind.ematch.instance] fthm: f (f (f x)) = f (f x)
-/
#guard_msgs (info) in
-- should not instantiate anything using pattern `f (f #0)`
set_option trace.grind.ematch.instance true in
example : f x = x := by
  fail_if_success grind only [fthm]
  sorry

/--
error: the modifier `usr` is only relevant in parameters for `grind only`
-/
#guard_msgs (error) in
example : f (f (f x)) = f x := by
  grind [usr fthm]

/--
error: invalid use of `usr` modifier, `fthm` does not have patterns specified with the command `grind_pattern`
-/
#guard_msgs (error) in
example : f (f (f x)) = f x := by
  grind only [usr fthm]

grind_pattern fthm => f (f x)

example : f (f (f x)) = f x := by
  grind only [usr fthm]

#guard_msgs (info) in
-- should not instantiate anything using pattern `f (f #0)`
set_option trace.grind.ematch.instance true in
example : f x = x := by
  fail_if_success grind only [usr fthm]
  sorry

/--
info: [grind.ematch.instance] fthm: f (f x) = f x
[grind.ematch.instance] fthm: f (f (f x)) = f (f x)
-/
#guard_msgs (info) in
set_option trace.grind.ematch.instance true in
example : f x = x := by
  fail_if_success grind only [fthm]
  sorry

/--
error: the modifier `usr` is only relevant in parameters for `grind only`
-/
#guard_msgs (error) in
example : f (f (f x)) = f x := by
  grind [usr fthm]
