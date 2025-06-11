/-!
# Testing the new behavior of the `show` tactic

Implemented in PR #7395.
-/

/-!
`show` can change a single goal to a definitionally equivalent one.
-/

/--
error: unsolved goals
x : Nat
⊢ x - 0 = 3 - 3
-/
#guard_msgs in
example : x = 0 := by
  show x - 0 = 3 - 3

/-!
`show` on a single goal fails if the pattern is not defeq to the target.
-/

/--
error: 'show' tactic failed, pattern
  x = 1
is not definitionally equal to target
  x = 0
-/
#guard_msgs in
example : x = 0 := by
  show x = 1

/-!
`show` on multiple goals picks the first that matches.
-/

/--
error: unsolved goals
case refine_2
x : Nat
⊢ x = 1

case refine_1
x : Nat
⊢ x = 0
-/
#guard_msgs in
example : x = 0 ∧ x = 1 := by
  and_intros
  show _ = 1

/-!
The matching goal is moved to the front and the order of the others is preserved.
-/

/--
error: unsolved goals
case refine_2.refine_2.refine_1
x : Nat
⊢ x = 2

case refine_1
x : Nat
⊢ x = 0

case refine_2.refine_1
x : Nat
⊢ x = 1

case refine_2.refine_2.refine_2
x : Nat
⊢ x = 3
-/
#guard_msgs in
example : x = 0 ∧ x = 1 ∧ x = 2 ∧ x = 3 := by
  and_intros
  show _ = 2

/-!
All goals are first elaborated without error recovery.
-/

/--
error: unsolved goals
case refine_2.refine_2
a : Unit
⊢ a = ()

case refine_1
⊢ () = ()

case refine_2.refine_1
⊢ () = ()
-/
#guard_msgs in
example : () = () ∧ () = () ∧ (∀ a, a = ()) := by
  and_intros; all_goals try intro a
  show a = _

/-!
The first goal is re-elaborated with error recovery.
-/

/--
error: unknown identifier 'a'
---
error: unsolved goals
case refine_1
⊢ sorry = ()

case refine_2
⊢ () = ()
-/
#guard_msgs in
example : () = () ∧ () = () := by
  and_intros
  show a = _

/-!
If all unifications fail, the error is from the first goal with a mention that the later goals
also weren't defeq.
-/

/--
error: 'show' tactic failed, no goals unify with the given pattern.

In the first goal, the pattern
  x = 4
is not definitionally equal to the target
  x = 1
(Errors for other goals omitted)
-/
#guard_msgs in
example : x = 1 ∧ x = 2 ∧ x = 3 := by
  and_intros
  show x = 4

/-!
`show` also works when a mentioned variable only exists in some goals.
-/

/--
error: unsolved goals
case refine_2.refine_2
c : Nat
⊢ c = 1

case refine_1
a : Nat
⊢ a = 1

case refine_2.refine_1
b : Nat
⊢ b = 1
-/
#guard_msgs in
example : (∀ a, a = 1) ∧ (∀ b, b = 1) ∧ (∀ c, c = 1) := by
  and_intros; all_goals unhygienic intro
  show c = _
