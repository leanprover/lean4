import Lean
/-!
# Tests of `Meta.decLevel?`
-/

open Lean Elab Term Command

elab "#dec_level " u:level : command => runTermElabM fun _ => do
  let u ← elabLevel u
  let u' ← Meta.decLevel u
  let u ← instantiateLevelMVars u
  let u' ← instantiateLevelMVars u'
  logInfo m!"({u'}) + 1 = {u}"

/-!
Cannot decrement zero.
-/
/-- error: invalid universe level, 0 is not greater than 0 -/
#guard_msgs in #dec_level 0

/-!
Decrementing positive constant.
-/
/-- info: (2) + 1 = 3 -/
#guard_msgs in #dec_level 3

/-!
Cannot decrement universe parameter.
-/
/-- error: invalid universe level, u is not greater than 0 -/
#guard_msgs in universe u in #dec_level u

/-!
Decrementing offset universe parameter
-/
/-- info: (u + 2) + 1 = u + 3 -/
#guard_msgs in universe u in #dec_level u+3

/-!
Decrement can assign.
-/
/-- info: (?u.2) + 1 = ?u.2 + 1 -/
#guard_msgs in #dec_level _

/-!
Cannot assign inside `max`.
-/
/-- error: invalid universe level, max ?u.2 ?u.1 is not greater than 0 -/
#guard_msgs in #dec_level max _ _
/-- error: invalid universe level, max ?u.1 3 is not greater than 0 -/
#guard_msgs in #dec_level max _ 3
/-- error: invalid universe level, max 3 ?u.1 is not greater than 0 -/
#guard_msgs in #dec_level max 3 _

/-!
Can assign inside `max` if one side is zero.
-/
/-- info: (?u.2) + 1 = ?u.2 + 1 -/
#guard_msgs in #dec_level max 0 _
/-- info: (?u.2) + 1 = ?u.2 + 1 -/
#guard_msgs in #dec_level max _ 0
/-- info: (?u.2) + 1 = ?u.2 + 1 -/
#guard_msgs in #dec_level max (imax 2 (max 0 0)) _

/-!
Can assign inside `imax` if first argument is zero
-/
/-- info: (?u.2) + 1 = ?u.2 + 1 -/
#guard_msgs in #dec_level imax 0 _
/-!
Can't decrement `imax _ 0`.
-/
/-- error: invalid universe level, 0 is not greater than 0 -/
#guard_msgs in #dec_level imax 5 0
/-!
Second argument of `imax` is assignable, if the first argument is zero or decrementable.
-/
/-- info: (max 4 ?u.2) + 1 = max 5 (?u.2 + 1) -/
#guard_msgs in #dec_level imax 5 _
/-- info: (?u.2) + 1 = ?u.2 + 1 -/
#guard_msgs in #dec_level imax 0 _
/-- error: invalid universe level, imax u ?u.1 is not greater than 0 -/
#guard_msgs in universe u in #dec_level imax u _

/-!
Tests of `max` decrementing both arguments.
-/
/-- info: (u) + 1 = u + 1 -/
#guard_msgs in universe u in #dec_level max 1 (u + 1)
/-- info: (max 1 u) + 1 = max 2 (u + 1) -/
#guard_msgs in universe u in #dec_level max 2 (u + 1)

/-!
Failure, since `u` cannot be decremented.
-/
/-- error: invalid universe level, max 1 u is not greater than 0 -/
#guard_msgs in universe u in #dec_level max 1 u
/-- error: invalid universe level, max u 1 is not greater than 0 -/
#guard_msgs in universe u in #dec_level max u 1
/-- error: invalid universe level, imax 1 u is not greater than 0 -/
#guard_msgs in universe u in #dec_level imax 1 u
/-- error: invalid universe level, max u 1 is not greater than 0 -/
#guard_msgs in universe u in #dec_level imax u 1
