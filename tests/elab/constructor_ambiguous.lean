/-!
Tests that `constructor` warns when more than one constructor of the target's inductive type
matches, that `constructor +first` and its shorthand `constructor!` suppress the warning, and that
the selected constructor and the resulting goals are otherwise unchanged.
-/

inductive Foo : Nat → Prop where
  | a : Foo 0
  | b : Foo 0
  | c : Foo 1

/--
warning: Tactic `constructor` applied constructor `Foo.a`, but `Foo.b` also matches the goal.

Hint: Use `constructor!` to apply the first matching constructor without this warning:
  [apply] constructor!
-/
#guard_msgs in
example : Foo 0 := by constructor

-- Only one constructor matches, so there is no warning.
#guard_msgs in
example : Foo 1 := by constructor

-- Inductive types with a single constructor never warn.
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

/--
warning: Tactic `constructor` applied constructor `Or.inl`, but `Or.inr` also matches the goal.

Hint: Use `constructor!` to apply the first matching constructor without this warning:
  [apply] constructor!
-/
#guard_msgs in
example : True ∨ True := by
  constructor
  trivial

inductive Bar where
  | a | b | c

-- More than two matching constructors are all reported.
/--
warning: Tactic `constructor` applied constructor `Bar.a`, but `Bar.b` and `Bar.c` also match the goal.

Hint: Use `constructor!` to apply the first matching constructor without this warning:
  [apply] constructor!
-/
#guard_msgs in
example : Bar := by constructor

-- `constructor!` and `constructor +first` silently select the first matching constructor.
#guard_msgs in
example : Foo 0 := by constructor!

#guard_msgs in
example : Foo 0 := by constructor +first

#guard_msgs in
example : True ∨ True := by
  constructor!
  trivial

-- `-first` explicitly requests the default behavior.
/--
warning: Tactic `constructor` applied constructor `Foo.a`, but `Foo.b` also matches the goal.

Hint: Use `constructor!` to apply the first matching constructor without this warning:
  [apply] constructor!
-/
#guard_msgs in
example : Foo 0 := by constructor -first

-- The ambiguity check does not disturb the goals produced by the selected constructor.
inductive Baz : Nat → Prop where
  | mk (h : True) (h' : False) : Baz 0
  | mk' : Baz 0

/--
warning: Tactic `constructor` applied constructor `Baz.mk`, but `Baz.mk'` also matches the goal.

Hint: Use `constructor!` to apply the first matching constructor without this warning:
  [apply] constructor!
---
error: unsolved goals
case h'
⊢ False
-/
#guard_msgs in
example : Baz 0 := by
  constructor
  · trivial

-- Failures are unchanged.
/--
error: Tactic `constructor` failed: target is not an inductive datatype

p q : Prop
⊢ p → q
-/
#guard_msgs in
example (p q : Prop) : p → q := by constructor

/--
error: Tactic `constructor` failed: no applicable constructor found

⊢ Foo 2
-/
#guard_msgs in
example : Foo 2 := by constructor

/--
error: Tactic `constructor` failed: no applicable constructor found

⊢ Foo 2
-/
#guard_msgs in
example : Foo 2 := by constructor!
