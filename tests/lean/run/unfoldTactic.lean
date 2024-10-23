/-!
# Tests of the `unfold` tactic
-/

/-!
Tests adapted from mathlib's `unfold_let` tactic
-/

example : let x := 1; let y := 2; x + y = y + x := by
  intro x y
  unfold x
  guard_target =ₛ 1 + y = y + 1
  let z := 3
  have h : z - 3 = 0 := rfl
  unfold z at h
  guard_hyp h :ₛ 3 - 3 = 0
  unfold y
  guard_target =ₛ 1 + 2 = 2 + 1
  rfl

example : let x := 1; let y := 2; x + y = y + x := by
  intro x y
  unfold x y
  guard_target =ₛ 1 + 2 = 2 + 1
  rfl

example : let x := 1; let y := 2 + x; y = 3 := by
  intro x y
  unfold y
  guard_target =ₛ 2 + x = 3
  unfold x
  guard_target =ₛ 2 + 1 = 3
  rfl

example : let x := 1; let y := 2 + x; y = 3 := by
  intro x y
  fail_if_success unfold x y -- wrong order
  unfold y x
  guard_target =ₛ 2 + 1 = 3
  rfl

/-!
Do not reorder hypotheses. (`unfold` makes a change)
-/
set_option linter.unusedVariables false in
example : let ty := Int; ty → Nat → Nat := by
  intro ty a a
  unfold ty at *
  exact a

/-!
Beta reduction of unfolded local functions
-/
example : True := by
  let f (x y : Nat) := x + y
  have : f 1 2 = 3 := by
    unfold f
    guard_target =ₛ 1 + 2 = 3
    rfl
  trivial

/-!
Nothing to unfold
-/
/--
error: tactic 'unfold' failed to unfold 'id' at
  True
-/
#guard_msgs in
example : True := by
  unfold id
/--
error: tactic 'unfold' failed to unfold 'x' at
  True
-/
#guard_msgs in
example : True := by
  let x := 2
  unfold x


/-!
Conv tactic
-/

example (h : False) : id true = false := by
  conv => unfold id
  guard_target =ₛ true = false
  exact h.elim

example : let x := 1; let y := 2; x + y = y + x := by
  intro x y
  conv => unfold x
  guard_target =ₛ 1 + y = y + 1
  rfl

/-!
Error: not a local definition
-/

/-- error: tactic 'unfold' failed, local variable 'x' has no definition -/
#guard_msgs in example (x : Nat) : x + 1 = 1 := by
  unfold x

  /-- error: conv tactic 'unfold' failed, local variable 'x' has no definition -/
#guard_msgs in example (x : Nat) : x + 1 = 1 := by
  conv => unfold x
