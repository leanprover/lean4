import Lean
/-!
# Tests of the `all_goals` tactic

This file aims to be a comprehensive test of the `all_goals` tactic combinator.
-/

open Lean Elab Tactic


/-!
Tactics may assign other goals. There are three goals, but the tactic is run twice.
-/
/--
info: case a
⊢ 1 ≤ ?m

case a
⊢ ?m ≤ 2

case m
⊢ Nat
---
info: running tac
running tac
-/
#guard_msgs in
example : 1 ≤ 2 := by
  apply Nat.le_trans
  trace_state
  all_goals trace "running tac"; first | apply Nat.le_refl | simp


/-!
Each failing tactic gets its own error message when in recovery mode.
There is no "unsolved goals" error.
-/
/--
error: type mismatch
  Eq.refl 3
has type
  3 = 3 : Prop
but is expected to have type
  false = false : Prop
---
error: type mismatch
  Eq.refl 3
has type
  3 = 3 : Prop
but is expected to have type
  true = true : Prop
-/
#guard_msgs in
example (b : Bool) : b = b := by
  cases b
  all_goals exact Eq.refl 3
  trace "shouldn't get here"


/-!
Even if at least one suceeds, the entire tactic fails if any fails, stopping the tactic script.
-/
/--
error: type mismatch
  Eq.refl true
has type
  true = true : Prop
but is expected to have type
  false = false : Prop
-/
#guard_msgs in
example (b : Bool) : b = b := by
  cases b
  all_goals exact Eq.refl true
  trace "shouldn't get here"


/-!
On failure, the metavar context is reverted. Here, `v` is temporarily assigned to `()` in the `true`
case (see the first 'unsolved goals'), but then afterwards it is unassigned.
-/
/--
error: unsolved goals
v : Unit := ()
this : () = v
⊢ True
---
error: unsolved goals
case refine_2.false
v : Unit := ?_ false
⊢ True

case refine_1
b : Bool
⊢ Unit
---
info: case refine_2.false
v : Unit := ?_ false
⊢ True

case refine_1
b : Bool
⊢ Unit
-/
#guard_msgs in
set_option pp.mvars false in
example (b : Bool) : True := by
  let v : Unit := ?_
  cases b
  case true =>
    all_goals (have : () = v := (by refine rfl); done)
  trace_state


/-!
On error, all goals are admitted. There are two `sorry`s in the prof term even though the tactic succeeds in one case.
-/

/--
error: type mismatch
  Eq.refl true
has type
  true = true : Prop
but is expected to have type
  false = false : Prop
---
info: Try this: Bool.casesOn (motive := fun t => b = t → b = b) b (fun h => Eq.symm h ▸ sorry) (fun h => Eq.symm h ▸ sorry)
  (Eq.refl b)
-/
#guard_msgs in
example (b : Bool) : b = b := by?
  cases b
  all_goals exact Eq.refl true


/-!
Each successive goal sees the metavariable assignments of the preceding ones, even if the preceding one failed.
-/
/--
error: Case tag 'true' not found.

The only available case tag is 'refine_2.false'.
---
info: case refine_2.false
v : Unit := ()
this : () = v
⊢ True
case refine_2.true
v : Unit := ()
⊢ True
---
info: true
-/
#guard_msgs in
example (b : Bool) : True := by
  let v : Unit := ?_
  cases b
  all_goals
    try case' false => have : () = v := (by refine rfl)
    trace_state
    case true => trace "true"; trivial
  trace "should not get here"


/-!
When not in recovery mode, the first error becomes an exception.
-/

elab "without_recover " tac:tactic : tactic => do
  withoutRecover <| evalTactic tac

/--
error: type mismatch
  Eq.refl 3
has type
  3 = 3 : Prop
but is expected to have type
  false = false : Prop
-/
#guard_msgs in
example (b : Bool) : b = b := by
  cases b
  without_recover all_goals exact Eq.refl 3


/-!
When `all_goals` fails outside recovery mode, state is completely rolled back.
This is the responsibility of `first`, but `all_goals` coordinates by being sure to throw an exception.
-/

/--
info: rfl
rfl
-/
#guard_msgs in
example (b : Bool) : b = b := by
  cases b
  first | (all_goals exact Eq.refl false) | (all_goals trace "rfl"; rfl)


/-!
Simple failure.
-/

/--
error: tactic 'fail' failed
⊢ True
---
info: Try this: sorry
-/
#guard_msgs in
example : True := by?
  all_goals fail
  trivial


/-!
Runtime exception
-/

elab "throw_max_rec_depth" : tactic => do
  throwMaxRecDepthAt (← getRef)
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
---
info: Try this: sorry
-/
#guard_msgs in
example : True := by?
  all_goals throw_max_rec_depth
  trivial


/-!
Regression test: `all_goals` should not catch interrupts.
-/
elab "interrupt" : tactic =>
  throw <| .internal Core.interruptExceptionId

/-- We never get to checking this docstring. Everything is completely interrupted. -/
#guard_msgs in
example : True := by?
  all_goals interrupt
  trivial


/-!
Various tests involving a `Weekday` type.
-/

inductive Weekday where
  | sunday    : Weekday
  | monday    : Weekday
  | tuesday   : Weekday
  | wednesday : Weekday
  | thursday  : Weekday
  | friday    : Weekday
  | saturday  : Weekday

def Weekday.next : Weekday -> Weekday :=
  fun d => match d with
    | sunday    => monday
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => saturday
    | saturday  => sunday

def Weekday.previous : Weekday -> Weekday
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

theorem Weekday.nextOfPrevious (d : Weekday) : next (previous d) = d := by
  cases d
  all_goals rfl

theorem Weekday.nextOfPrevious' (d : Weekday) : previous (next d) = d ∧ next (previous d) = d := by
  apply And.intro
  cases d <;> rfl
  cases d <;> rfl

theorem Weekday.nextOfPrevious'' (d : Weekday) : previous (next d) = d ∧ next (previous d) = d := by
  apply And.intro <;> cases d <;> rfl

open Lean.Parser.Tactic in
macro "rwd " x:term : tactic => `(tactic| (rw [$x:term]; done))

theorem ex (a b c : α) (h₁ : a = b) (h₂ : a = c) : b = a ∧ c = a := by
  apply And.intro <;> first | rwd h₁ | rwd h₂

theorem idEq (a : α) : id a = a :=
  rfl

/--
info: case sunday
⊢ Weekday.sunday.previous.next = id Weekday.sunday

case monday
⊢ Weekday.monday.previous.next = id Weekday.monday

case tuesday
⊢ Weekday.tuesday.previous.next = id Weekday.tuesday

case wednesday
⊢ Weekday.wednesday.previous.next = id Weekday.wednesday

case thursday
⊢ Weekday.thursday.previous.next = id Weekday.thursday

case friday
⊢ Weekday.friday.previous.next = id Weekday.friday

case saturday
⊢ Weekday.saturday.previous.next = id Weekday.saturday
---
info: case sunday
⊢ Weekday.sunday.previous.next = Weekday.sunday

case monday
⊢ Weekday.monday.previous.next = Weekday.monday

case tuesday
⊢ Weekday.tuesday.previous.next = Weekday.tuesday

case wednesday
⊢ Weekday.wednesday.previous.next = Weekday.wednesday

case thursday
⊢ Weekday.thursday.previous.next = Weekday.thursday

case friday
⊢ Weekday.friday.previous.next = Weekday.friday

case saturday
⊢ Weekday.saturday.previous.next = Weekday.saturday
-/
#guard_msgs in
theorem Weekday.test (d : Weekday) : next (previous d) = id d := by
  cases d
  trace_state
  all_goals rw [idEq]
  trace_state
  all_goals rfl

/--
info: case sunday
⊢ Weekday.sunday.previous.next = Weekday.sunday

case monday
⊢ Weekday.monday.previous.next = Weekday.monday

case tuesday
⊢ Weekday.tuesday.previous.next = Weekday.tuesday

case wednesday
⊢ Weekday.wednesday.previous.next = Weekday.wednesday

case thursday
⊢ Weekday.thursday.previous.next = Weekday.thursday

case friday
⊢ Weekday.friday.previous.next = Weekday.friday

case saturday
⊢ Weekday.saturday.previous.next = Weekday.saturday
-/
#guard_msgs in
theorem Weekday.test2 (d : Weekday) : next (previous d) = id d := by
  cases d <;> rw [idEq]
  trace_state
  all_goals rfl

def bug {a b c : Nat} (h₁ : a = b) (h₂ : b = c) : a = c := by
  apply Eq.trans <;> assumption
