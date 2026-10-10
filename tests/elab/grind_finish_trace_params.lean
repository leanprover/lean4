module

/-!
`finish?` suggestions are validated at the goal before the parameters are asserted.

Previously, when the parameters alone closed the goal, the empty script `done` was validated
at a goal whose fact queue was still pending, producing a spurious "generated tactic cannot
close the goal" warning.
-/

def f (n : Nat) := n + 3

theorem f_inj : Function.Injective f := by
  intro a b h
  simp [f] at h
  omega

/--
info: Try this:
  [apply] finish only [inj f_inj]
-/
#guard_msgs in
example (a b : Nat) (h : f a = f b) : a = b := by
  grind => finish? [inj f_inj]

example (a b : Nat) (h : f a = f b) : a = b := by
  grind => finish [inj f_inj]

def g (n : Nat) := n

theorem g_eq (n : Nat) : g n = n := rfl

/--
info: Try this:
  [apply] finish only [g_eq 0]
-/
#guard_msgs in
example : g 0 = 0 := by
  grind => finish? [g_eq 0]

example : g 0 = 0 := by
  grind => finish [g_eq 0]

/-! A parameter fact of a `cases eager` type splits the goal; `finish` must close every branch. -/

inductive P : Prop
  | a | b

attribute [grind cases eager] P

theorem mkP : P := .a

example (f : Nat → Nat) (h : ∀ x, f x = x) : f 0 = 0 := by
  grind => finish [(mkP)]

/--
info: Try this:
  [apply] finish only [#7d84, (mkP)]
-/
#guard_msgs in
example (f : Nat → Nat) (h : ∀ x, f x = x) : f 0 = 0 := by
  grind => finish? [(mkP)]
