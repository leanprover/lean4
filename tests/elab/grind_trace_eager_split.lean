module

/-!
`grind?` must produce a script for every goal created during initialization.

A parameter fact whose type is marked `cases eager` splits the goal while the parameters are
asserted, i.e., before the traced `finish` runs. Previously, `grind?` only handled the first goal
and failed with "proof contains unresolved internal metavariable".
-/

inductive P : Prop
  | a | b

attribute [grind cases eager] P

theorem mkP : P := .a

example (f : Nat → Nat) (h : ∀ x, f x = x) : f 0 = 0 := by
  grind [(mkP)]

/--
info: Try these:
  [apply] grind only [#7d84, (mkP)]
  [apply] grind only [(mkP)]
  [apply] grind [(mkP)] =>
    · instantiate only [#7d84]
    · instantiate only [#7d84]
-/
#guard_msgs in
example (f : Nat → Nat) (h : ∀ x, f x = x) : f 0 = 0 := by
  grind? [(mkP)]

/-! A hypothesis of a `cases eager` type is split inside `finish`, not during initialization. -/

/--
info: Try these:
  [apply] grind only [#7d84]
  [apply] grind only
  [apply] grind => instantiate only [#7d84]
-/
#guard_msgs in
example (f : Nat → Nat) (h : ∀ x, f x = x) (_ : P) : f 0 = 0 := by
  grind?
