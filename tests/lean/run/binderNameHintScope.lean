import Lean

-- This checks that binderNameHint freshens up a variable.:

axiom allPairs (l : List α) (p : α → α → Bool) : Bool

#guard_msgs (drop warning) in
theorem all_eq_allPairs (l : List α) (p : α → Bool) :
    l.all p ↔ ∀ x y z, binderNameHint x p <| binderNameHint y () <| p x && p y && p z:= sorry

-- below we should get `a` from the user (no dagger), `y` with dagger (binderNameHint added a macro
-- scope) and `z` without dagger (because intro1P is not hygienic)

/--
error: tactic 'fail' failed
f : String → Bool
names : List String
a y✝ z : String
⊢ (f a && f y✝ && f z) = true
-/
#guard_msgs in
open Lean Elab Tactic in
example {f : String → Bool} (names : List String) : names.all (fun a => f a) = true := by
  rw [all_eq_allPairs]
  run_tac liftMetaTactic1 ((some ·.2) <$> ·.intro1P)
  run_tac liftMetaTactic1 ((some ·.2) <$> ·.intro1P)
  run_tac liftMetaTactic1 ((some ·.2) <$> ·.intro1P)
  fail
