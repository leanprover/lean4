
module
/-!
# Test for `grind +locals` flag (using the module system)

This tests that `grind +locals` adds local definitions from the current file.

We have a separate test here as the current semantics for `isImplementationDetail` are poorly specified,
and we've had to work around it in deciding which declarations should be included via `+locals`.
-/

-- A simple definition that provides an equation grind can use
def foo (n : Nat) : Nat := n + 1

-- Without +locals, grind shouldn't know about foo
-- (This test verifies +locals is actually doing something)
/--
error: `grind` failed
case grind
n : Nat
h : ¬foo n = n + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬foo n = n + 1
  [eqc] False propositions
    [prop] foo n = n + 1
  [cutsat] Assignment satisfying linear constraints
    [assign] n := 0
    [assign] foo n := 2
-/
#guard_msgs in
example (n : Nat) : foo n = n + 1 := by grind

-- Test that grind +locals can use the equation `foo n = n + 1`
example (n : Nat) : foo n = n + 1 := by grind +locals

-- An irrelevant definition that should NOT appear in grind? suggestions
def bar (n : Nat) : Nat := n * 2

-- Test that grind? +locals suggests only the relevant definition (foo), not bar
/--
info: Try these:
  [apply] grind only [foo]
  [apply] grind => instantiate only [foo]
-/
#guard_msgs in
example (n : Nat) : foo n = n + 1 := by grind? +locals

-- Test with a definition that has multiple equations via pattern matching
def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false

example : isZero 0 = true := by grind +locals
example (n : Nat) : isZero (n + 1) = false := by grind +locals
