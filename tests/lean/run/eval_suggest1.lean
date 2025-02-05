import Lean.Elab.Tactic.Try
import Std.Tactic.BVDecide

open Lean Elab Tactic Try
elab tk:"eval_suggest" tac:tactic : tactic => do
  evalAndSuggest tk tac

set_option hygiene false in
macro "try_simple?" : tactic => `(tactic| eval_suggest (intros; attempt_all | rfl | (first | simp; done | simp +arith; done) | grind | grind?))

opaque f : Nat → Nat
@[simp, grind =] theorem fthm : f x = x := sorry

/--
info: Try these:
• simp +arith
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
• · intros; grind
• · intros; grind only
-/
#guard_msgs (info) in
example (x : Nat) : True → x + 1 = Nat.succ x := by
  try_simple?
