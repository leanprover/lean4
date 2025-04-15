opaque f : Nat → Nat

@[grind] theorem fthm : f (f x) = f x := sorry

theorem fthm' : f (f x) = x := sorry

/--
error: `fthm'` is not marked with the `[grind]` attribute
-/
#guard_msgs in
attribute [-grind] fthm'

set_option trace.grind.assert true

/--
info: [grind.assert] ¬f (f (f a)) = f a
[grind.assert] f (f a) = f a
-/
#guard_msgs (info) in
example : f (f (f a)) = f a := by
  grind

attribute [-grind] fthm

/--
error: unsolved goals
a : Nat
⊢ f (f (f a)) = f a
---
info: [grind.assert] ¬f (f (f a)) = f a
-/
#guard_msgs (info, error) in
example : f (f (f a)) = f a := by
  fail_if_success grind

/--
error: `fthm` is not marked with the `[grind]` attribute
-/
#guard_msgs in
attribute [-grind] fthm

attribute [grind] fthm

example : f (f (f a)) = f a := by
  grind

def g (x : Nat) :=
  match x with
  | 0 => 1
  | x+1 => 2 * g x

attribute [grind] g

example : g a = b → a = 0 → b = 1 := by
  grind

attribute [-grind] g

/--
error: unsolved goals
a b : Nat
⊢ g a = b → a = 0 → b = 1
---
info: [grind.assert] g a = b
[grind.assert] a = 0
[grind.assert] ¬b = 1
-/
#guard_msgs (info, error) in
example : g a = b → a = 0 → b = 1 := by
  fail_if_success grind

/--
error: `g` is not marked with the `[grind]` attribute
-/
#guard_msgs in
attribute [-grind] g
