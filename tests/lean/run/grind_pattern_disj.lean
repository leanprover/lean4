/-
Test for grind_pattern with disjunction support (CNF constraints)

This test demonstrates that the `or` constraint is actually working.
Without the disjunction, we would need two separate patterns.
-/

-- Define a custom binary operation with a commutativity property
-- We want to use this theorem ONLY when at least one argument is not a concrete value
-- to avoid unnecessary instantiations on fully concrete terms
structure MyType where
  val : Nat
  deriving DecidableEq, Inhabited

def myOp (x y : MyType) : MyType := ⟨x.val + y.val⟩

-- This axiom is expensive to apply on concrete terms, so we guard it
axiom myOp_comm {x y : MyType} : myOp x y = myOp y x

-- Key: Use disjunction to allow EITHER x or y to be symbolic (but not both concrete)
grind_pattern myOp_comm => myOp x y where
  not_value x or not_value y

-- Test 1: Symbolic x, concrete y - should work
example (a : MyType) : myOp a ⟨5⟩ = myOp ⟨5⟩ a := by
  grind

-- Test 2: Concrete x, symbolic y - should work
example (b : MyType) : myOp ⟨3⟩ b = myOp b ⟨3⟩ := by
  grind

-- Test 3: Both symbolic - should work
example (a b : MyType) : myOp a b = myOp b a := by
  grind

-- Test 4: Both concrete - should NOT work (pattern prevented by not_value constraint)
set_option warn.sorry false in
example : myOp ⟨3⟩ ⟨5⟩ = myOp ⟨5⟩ ⟨3⟩ := by
  fail_if_success grind
  sorry

-- Negative test cases: guard and check cannot be in disjunctions

-- Test: Error case - guard in disjunction should be rejected
axiom dummy1 {a b : Nat} : a < b → a % b = a

/--
error: `guard` and `check` constraints cannot be used in disjunctions
-/
#guard_msgs in
grind_pattern dummy1 => a % b where
  guard (a < b) or not_value a

-- Test: Error case - check in disjunction should be rejected
axiom dummy2 {a b : Nat} : a < b → a % b = a

/--
error: `guard` and `check` constraints cannot be used in disjunctions
-/
#guard_msgs in
grind_pattern dummy2 => a % b where
  check (a < b) or not_value a
