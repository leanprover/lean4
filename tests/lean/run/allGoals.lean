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
trace: case a
⊢ 1 ≤ ?m

case a
⊢ ?m ≤ 2

case m
⊢ Nat
---
trace: running tac
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
Even if at least one succeeds, the entire tactic fails if any fails, stopping the tactic script.
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
trace: case refine_2.false
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
On error, failing goals are admitted. There is one `sorry` in the proof term corresponding to the failing case.
-/

/--
error: type mismatch
  Eq.refl true
has type
  true = true : Prop
but is expected to have type
  false = false : Prop
---
info: Try this: Bool.casesOn (motive := fun t => b = t → b = b) b (fun h => Eq.symm h ▸ sorry)
  (fun h => Eq.symm h ▸ Eq.refl true) (Eq.refl b)
-/
#guard_msgs in
example (b : Bool) : b = b := by?
  cases b
  all_goals exact Eq.refl true


/-!
If the tactic fails on a particular goal, then the state is restored, while preserving log messages.
This allows the tactic to run on all goals, which is most useful in interactive mode.
In this test, we see `v : Unit := ?_ true` in the `refine_2.true` case,
even though the metavariable is assigned in the `refine_2.false` case before the "case tag 'true' not found" error.
-/
set_option pp.mvars false in
/--
error: Case tag 'true' not found.

The only available case tag is 'refine_2.false'.
---
error: Case tag 'true' not found.

The only available case tag is 'refine_1'.
---
trace: case refine_2.false
v : Unit := ()
this : () = v
⊢ True
case refine_2.true
v : Unit := ?_ true
⊢ True
case refine_1
b : Bool
⊢ Unit
---
trace: in true
-/
#guard_msgs in
example (b : Bool) : True := by
  let v : Unit := ?_
  cases b
  all_goals
    try case' false => have : () = v := (by refine rfl)
    trace_state
    case true => trace "in true"; trivial
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
trace: rfl
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
  throwInterruptException

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
trace: case sunday
⊢ sunday.previous.next = id sunday

case monday
⊢ monday.previous.next = id monday

case tuesday
⊢ tuesday.previous.next = id tuesday

case wednesday
⊢ wednesday.previous.next = id wednesday

case thursday
⊢ thursday.previous.next = id thursday

case friday
⊢ friday.previous.next = id friday

case saturday
⊢ saturday.previous.next = id saturday
---
trace: case sunday
⊢ sunday.previous.next = sunday

case monday
⊢ monday.previous.next = monday

case tuesday
⊢ tuesday.previous.next = tuesday

case wednesday
⊢ wednesday.previous.next = wednesday

case thursday
⊢ thursday.previous.next = thursday

case friday
⊢ friday.previous.next = friday

case saturday
⊢ saturday.previous.next = saturday
-/
#guard_msgs in
theorem Weekday.test (d : Weekday) : next (previous d) = id d := by
  cases d
  trace_state
  all_goals rw [idEq]
  trace_state
  all_goals rfl

/--
trace: case sunday
⊢ sunday.previous.next = sunday

case monday
⊢ monday.previous.next = monday

case tuesday
⊢ tuesday.previous.next = tuesday

case wednesday
⊢ wednesday.previous.next = wednesday

case thursday
⊢ thursday.previous.next = thursday

case friday
⊢ friday.previous.next = friday

case saturday
⊢ saturday.previous.next = saturday
-/
#guard_msgs in
theorem Weekday.test2 (d : Weekday) : next (previous d) = id d := by
  cases d <;> rw [idEq]
  trace_state
  all_goals rfl

def bug {a b c : Nat} (h₁ : a = b) (h₂ : b = c) : a = c := by
  apply Eq.trans <;> assumption

/-!
`all_goals` was not correctly backtracking state
https://github.com/leanprover/lean4/issues/7883
There was an error because the metavariable state was being restored but not the goal list.
-/
/-- error: dsimp made no progress -/
#guard_msgs in
theorem foo : ∃ f : Unit → Unit, f () = () := by
  refine ⟨fun x => ?f_old, ?hf⟩
  all_goals dsimp
/-!
Another example from the comments of https://github.com/leanprover/lean4/issues/7883
-/
/--
error: tactic 'fail' failed
⊢ True
-/
#guard_msgs in
example : True := by
  all_goals (refine ?_; fail)
