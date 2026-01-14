/-!
# Test for `simp +locals` flag

This tests that `simp +locals` adds local definitions from the current file.
-/

-- A simple definition that provides an equation simp can use
def foo (n : Nat) : Nat := n + 1

-- Without +locals, simp shouldn't know about foo
-- (This test verifies +locals is actually doing something)
/--
error: `simp` made no progress
-/
#guard_msgs in
example (n : Nat) : foo n = n + 1 := by simp

-- Test that simp +locals can use the equation `foo n = n + 1`
example (n : Nat) : foo n = n + 1 := by simp +locals

-- An irrelevant definition that should NOT appear in simp? suggestions
def bar (n : Nat) : Nat := n * 2

-- Test that simp? +locals suggests only the relevant definition (foo), not bar
/--
info: Try this:
  [apply] simp only [foo, Nat.add_left_cancel_iff]
-/
#guard_msgs in
example (n : Nat) : foo n = n + 1 := by simp? +locals

-- Test with a definition that has multiple equations via pattern matching
def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false

example : isZero 0 = true := by simp +locals
example (n : Nat) : isZero (n + 1) = false := by simp +locals

-- Test simp_all +locals
example (n : Nat) (h : n = 0) : isZero n = true := by simp_all +locals

-- Test dsimp +locals
example : foo 5 = 6 := by dsimp +locals
