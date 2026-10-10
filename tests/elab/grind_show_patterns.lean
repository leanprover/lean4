module

/-!
Test `show_patterns` in `grind` tactic mode (#11996): active and explicitly selected theorems,
local hypotheses, multi-patterns, theorem modifiers, and inspection without instantiation.
-/

set_option warn.sorry false
reset_grind_attrs%

public opaque f : Nat → Nat
public opaque g : Nat → Nat
public opaque p : Nat → Prop
public opaque q : Nat → Prop
public axiom fax : f (x + 1) = g (f x)
public axiom pq : p x → q x

-- Include both newly activated theorems and those used in a previous E-matching round.
/--
trace: [ematch] E-matching patterns
  [thm] fax: [f (#0 + 1)]
  [thm] pq: [p #1]
---
trace: [ematch] E-matching patterns
---
trace: [ematch] E-matching patterns
  [thm] fax: [f (#0 + 1)]
  [thm] pq: [p #1]
-/
#guard_msgs in
example : f (x + 5) = a := by
  grind only [= fax, → pq] =>
    show_patterns
    show_patterns []
    instantiate
    show_patterns
    sorry

-- Explicit inspection must neither activate a theorem nor instantiate it.
/--
trace: [ematch] E-matching patterns
  [thm] fax: [f (#0 + 1)]
---
trace: [ematch] E-matching patterns
-/
#guard_msgs in
example : f (x + 1) = g (f x) := by
  grind only =>
    show_patterns [fax]
    show_patterns
    fail_if_success instantiate
    use [fax]

/--
trace: [ematch] E-matching patterns
---
trace: [ematch] E-matching patterns
-/
#guard_msgs in
example : False := by
  grind only =>
    show_patterns
    show_patterns []
    sorry

section
attribute [local grind →] pq

-- An unrelated registered theorem is not active merely because it is available to `grind`.
/-- trace: [ematch] E-matching patterns -/
#guard_msgs in
example : f x = a := by
  grind =>
    show_patterns
    sorry
end

/--
trace: [ematch] E-matching patterns
  [thm] h: [p #1]
  [thm] h: [q #1]
-/
#guard_msgs in
example (h : ∀ x, p x → q x) (hp : p a) : q a := by
  grind (revert := false) only =>
    show_patterns
    instantiate

/--
trace: [ematch] E-matching patterns
  [thm] h: [p #1]
  [thm] h: [p (f #1)]
  [thm] h: [f #1]
-/
#guard_msgs in
example (h : ∀ x, p x → p (f x)) (hp : p a) : p (f a) := by
  grind (revert := false) only =>
    show_patterns [#bfb8]
    use [#bfb8]

public opaque r : Nat → Nat → Prop
public axiom rtrans {x y z} : r x y → r y z → r x z
grind_pattern rtrans => r x y, r y z

/--
trace: [ematch] E-matching patterns
  [thm] rtrans: [r #4 #3, r #3 #2]
-/
#guard_msgs in
example : r a b → r b c → r a c := by
  grind =>
    show_patterns [usr rtrans]
    instantiate

-- Use the same modifier semantics as `instantiate`, including both equality directions.
/--
trace: [ematch] E-matching patterns
  [thm] fax: [f (#0 + 1)]
  [thm] fax: [g (f #0)]
-/
#guard_msgs in
example : False := by
  grind only =>
    show_patterns [_=_ fax]
    sorry

public axiom nested : f (f x) = f x

/--
trace: [ematch] E-matching patterns
  [thm] nested: [f #0]
-/
#guard_msgs in
example : False := by
  grind only =>
    show_patterns [!nested,]
    sorry

public def twice (x : Nat) : Nat := f (f x)

/--
trace: [ematch] E-matching patterns
  [thm] twice.eq_1: [twice #0]
-/
#guard_msgs in
example : False := by
  grind only =>
    show_patterns [twice]
    sorry

namespace Selected
public axiom pq' : p x → q x
attribute [scoped grind →] pq'
end Selected

/--
trace: [ematch] E-matching patterns
  [thm] Selected.pq': [p #1]
-/
#guard_msgs in
example : False := by
  grind only =>
    show_patterns [namespace Selected]
    sorry

/-- error: no local theorems -/
#guard_msgs in
example : False := by
  grind only => show_patterns [#abcd]

/-- error: invalid anchor, value is too big -/
#guard_msgs in
example : False := by
  grind only => show_patterns [#10000000000000000]

/-- error: invalid modifier -/
#guard_msgs in
example : False := by
  grind only => show_patterns [cases fax]

/--
error: invalid use of `usr` modifier, `fax` does not have patterns specified with the command `grind_pattern`
-/
#guard_msgs in
example : False := by
  grind only => show_patterns [usr fax]

-- Inspect the explicitly supplied theorem in the original repeated-instantiation regression.
/--
trace: [ematch] E-matching patterns
  [thm] fax: [f (#0 + 1)]
---
error: `instantiate` tactic failed to instantiate new facts
Use `show_patterns` to inspect active theorem patterns, or `show_patterns [thm₁, ...]` to inspect specific theorems.
-/
#guard_msgs in
example : f (x + 5) = a := by
  grind only =>
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax]
    show_patterns [fax]
    use [fax]
