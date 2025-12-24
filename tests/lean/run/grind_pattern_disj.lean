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

-- Key: Use disjunction to allow EITHER x <|> y to be symbolic (but not both concrete)
grind_pattern myOp_comm => myOp x y where
  not_value x <|> not_value y

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

/-
Note: `guard` and `check` constraints cannot appear in disjunctions because they use
`termParser` which would consume the `<|>` as part of the term. The parser structure
naturally prevents this: guards/checks are parsed as alternatives to sepBy1, not as
atoms within sepBy1.
-/
