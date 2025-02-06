import Lean.Elab.Tactic.Try
import Std.Tactic.BVDecide

open Lean Elab Tactic Try
elab tk:"eval_suggest" tac:tactic : tactic => do
  evalAndSuggest tk tac

set_option hygiene false in
macro "try_simple?" : tactic => `(tactic| eval_suggest (intros; attempt_all | rfl | (first | simp?; done | simp? +arith; done | simp_all) | grind?))

opaque f : Nat → Nat
@[simp, grind =] theorem fthm : f x = x := sorry

/--
info: Try these:
• simp +arith
• simp +arith only [Nat.reduceAdd, fthm]
• grind
• grind only [= fthm]
-/
#guard_msgs (info) in
example (x : Nat) : 1 + 1 + f x = x + 2 := by
  try_simple?

/--
info: Try these:
• rfl
• simp
• simp only [Nat.succ_eq_add_one]
• grind
• grind only
-/
#guard_msgs (info) in
example (x : Nat) : x + 1 = Nat.succ x := by
  try_simple?

/--
info: Try these:
• · intros; rfl
• · intros; simp
• · intros; simp only [Nat.succ_eq_add_one]
• · intros; grind
• · intros; grind only
-/
#guard_msgs (info) in
example (x : Nat) : True → x + 1 = Nat.succ x := by
  try_simple?

/--
info: Try these:
• simp_all
• grind
• grind only
-/
#guard_msgs (info) in
example (h : 0 + x = y) : f x = f y := by
  try_simple?


macro "bad_tac" : tactic => `(tactic| eval_suggest (intros; (attempt_all | rfl | grind?); simp))

/--
error: invalid occurrence of `attempt_all` in non-terminal position for `try?` script
  (intros;
    (attempt_all
      | rfl
      | grind?);
    simp)
-/
#guard_msgs (error) in
example : True := by
  bad_tac

macro "simple_tac" : tactic => `(tactic| eval_suggest (intros; skip; first | skip | simp))

/--
info: Try this: simp
-/
#guard_msgs (info) in
example : True ∧ True := by
  simple_tac -- terminal `skip` should not succeed

example : False := by
  fail_if_success simple_tac -- should not succeed
  sorry
