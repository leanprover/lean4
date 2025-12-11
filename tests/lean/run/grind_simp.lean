/-!
# Tests for `grind +simp`

This file tests the `grind +simp` feature, which allows grind to use all `@[simp]` lemmas
as E-matching theorems.
-/

-- Test basic simp lemma usage
def foo (n : Nat) : Nat := n + 1
def bar (n : Nat) : Nat := 1 + n

@[simp] theorem foo_eq_bar : foo n = bar n := by simp [foo, bar, Nat.add_comm]

-- Verify plain grind fails but grind +simp succeeds
example : foo 5 = bar 5 := by
  fail_if_success grind
  grind +simp

-- Verify grind? +simp suggests the simp lemma
/--
info: Try these:
  [apply] grind only [= foo_eq_bar]
  [apply] grind => instantiate only [= foo_eq_bar]
-/
#guard_msgs in
example : foo 5 = bar 5 := by grind? +simp

-- Test that +simp can be combined with hypotheses
def qux (n : Nat) : Nat := n

@[simp] theorem qux_id : qux n = n := rfl

example (h : a = b) : qux a = b := by
  fail_if_success grind
  grind +simp

opaque P : Nat → Prop
@[simp] axiom p : P 37

example : P 37 := by
  fail_if_success grind
  grind +simp

-- Test that grind +simp works with standard library simp lemmas
-- String.length_append is currently @[simp] but not @[grind]
-- (It's fine to delete this without replacement once we add `grind` annotations to String lemmas.)
/--
info: Try these:
  [apply] grind only [= String.length_append]
  [apply] grind => instantiate only [= String.length_append]
-/
#guard_msgs in
example (s t : String) : (s ++ t).length = s.length + t.length := by
  fail_if_success grind
  grind? +simp
