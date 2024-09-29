/-!
# Make `..` do-what-I-mean in `refine`

The implementation of `..` for applications and structure instances inserts `_`'s.
For `refine`, we want unsolved-for `..` arguments to become new goals,
but we otherwise want them to behave like natural metavariables.
-/

/-!
Example function, `refine` creates new goals named using the parameter names.
-/

theorem foo (n : Nat) (m : Fin n) : True := trivial

example : True := by
  refine foo ..
  case m => exact (0 : Fin 1)

example : True := by
  refine foo ..
  case n => exact 1
  case m => exact (0 : Fin 1)

/-!
Fails with `exact` like before.
-/
/--
error: don't know how to synthesize implicit argument 'm'
  foo ?_ ?_
context:
⊢ Fin ?_
---
error: don't know how to synthesize implicit argument 'n'
  foo ?_ ?_
context:
⊢ Nat
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
set_option pp.mvars false in
example : True := by
  exact foo ..

/-!
Limitation: this feature does not work under binders since the natural metavariables get assigned
-/
/--
error: don't know how to synthesize implicit argument 'm'
  foo (?_ n) (?_ n)
context:
n : Nat
⊢ Fin (?_ n)
---
error: don't know how to synthesize implicit argument 'n'
  foo (?_ n) (?_ n)
context:
n : Nat
⊢ Nat
---
error: unsolved goals
⊢ Nat → True
-/
#guard_msgs in
set_option pp.mvars false in
example : Nat → True := by
  refine fun n => foo ..

/-!
Similar behavior with structures.
-/

structure S where
  a : Nat
  b : Nat

example : S := by
  refine { .. }
  case a => exact 1
  case b => exact 2

/--
error: don't know how to synthesize placeholder
context:
⊢ Nat
---
error: unsolved goals
⊢ S
-/
#guard_msgs in
example : S := by
  exact { a := 1, .. }

/-!
Limitation: `..` doesn't work underneath binders.
-/
/--
error: don't know how to synthesize placeholder
context:
n : Nat
⊢ Nat
---
error: don't know how to synthesize placeholder
context:
n : Nat
⊢ Nat
---
error: unsolved goals
⊢ Nat → S
-/
#guard_msgs in
example : Nat → S := by
  refine fun n => { .. }
