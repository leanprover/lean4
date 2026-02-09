module
public meta import Lean.Elab.Tactic
public import Lean.Elab.Tactic.Try
public import Std.Tactic.BVDecide

open Lean Elab Tactic Try
elab tk:"eval_suggest" tac:tactic : tactic => do
  evalAndSuggest tk tac (originalMaxHeartbeats := 10^8)

set_option hygiene false in
macro "try_simple?" : tactic => `(tactic| eval_suggest (intros; attempt_all | rfl | (first | simp?; done | simp? +arith; done | simp_all) | grind?))

opaque f : Nat → Nat
@[simp, grind =] theorem fthm : f x = x := sorry

/--
info: Try these:
  [apply] simp +arith
  [apply] simp +arith only [Nat.reduceAdd, fthm]
  [apply] grind
  [apply] grind only [= fthm]
  [apply] grind => instantiate only [= fthm]
-/
#guard_msgs (info) in
example (x : Nat) : 1 + 1 + f x = x + 2 := by
  try_simple?

/--
info: Try these:
  [apply] rfl
  [apply] simp
  [apply] simp only [Nat.succ_eq_add_one, Nat.add_left_cancel_iff]
  [apply] grind
  [apply] grind only
-/
#guard_msgs (info) in
example (x : Nat) : x + 1 = Nat.succ x := by
  try_simple?

/--
info: Try these:
  [apply] · intros; rfl
  [apply] · intros; simp
  [apply] · intros; simp only [Nat.succ_eq_add_one, Nat.add_left_cancel_iff]
  [apply] · intros; grind
  [apply] · intros; grind only
-/
#guard_msgs (info) in
example (x : Nat) : True → x + 1 = Nat.succ x := by
  try_simple?

/--
info: Try these:
  [apply] simp_all
  [apply] grind
  [apply] grind only
-/
#guard_msgs (info) in
example (h : 0 + x = y) : f x = f y := by
  try_simple?


macro "bad_tac" : tactic => `(tactic| eval_suggest (intros; (attempt_all | rfl | grind?); simp))

/--
error: Tactic `try?` failed: consider using `grind` manually, or `try? +missing` for partial proofs containing `sorry`

⊢ True
-/
#guard_msgs (error) in
example : True := by
  bad_tac

macro "simple_tac" : tactic => `(tactic| eval_suggest (intros; skip; first | skip | simp))

/--
info: Try this:
  [apply] simp
-/
#guard_msgs (info) in
example : True ∧ True := by
  simple_tac -- terminal `skip` should not succeed

example : False := by
  fail_if_success simple_tac -- should not succeed
  sorry

set_option hygiene false in
macro "simple_tac2" : tactic => `(tactic| eval_suggest (intros; (simp only [Nat.zero_add]; simp only [Nat.one_mul]); simp [*]))

/--
info: Try this:
  [apply] · intros; simp only [Nat.zero_add]; simp only [Nat.one_mul]; simp [*]
-/
#guard_msgs (info) in
example : x = 0 → 0 + 1*x = 0 := by
  simple_tac2

example : x = 0 → 0 + 1*x = 0 := by
  · intros; (simp only [Nat.zero_add]; simp only [Nat.one_mul]); simp [*]
