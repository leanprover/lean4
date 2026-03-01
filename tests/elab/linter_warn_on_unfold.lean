module

set_option linter.warnOnUnfold true
set_option linter.unusedVariables false

/-! # Tests for linter.warnOnUnfold

This linter detects when code relies on `Id α` being definitionally equal to `α`.
-/

-- Case 1: Nat literal in Id Nat context.
-- The OfNat instance for Id synthesizes a term of type `Id Nat` directly,
-- so the linter does not detect this case (known limitation).
#guard_msgs in
def test1 : Id Nat := 42

-- Case 2: Variable of type Id Nat used where Nat expected
/--
warning: This code relies on the definitional equality `Id α = α`.

Note: This linter can be disabled with `set_option linter.warnOnUnfold false`
-/
#guard_msgs in
def test2 (x : Id Nat) : Nat := x

-- Case 3: Id.run (proper API, should not warn)
#guard_msgs in
def test3 : Nat := Id.run do return 42

-- Case 4: pure (proper API, should not warn)
#guard_msgs in
def test4 : Id Nat := pure 42

-- Case 5: No Id involvement at all
#guard_msgs in
def test5 : Nat := 42

-- Case 6: Id Nat variable passed to function expecting Nat
/--
warning: This code relies on the definitional equality `Id α = α`.

Note: This linter can be disabled with `set_option linter.warnOnUnfold false`
-/
#guard_msgs in
def test6 (x : Id Nat) : Nat := Nat.succ x

-- Case 7: List (Id Nat) used where List Nat expected
/--
warning: This code relies on the definitional equality `Id α = α`.

Note: This linter can be disabled with `set_option linter.warnOnUnfold false`
-/
#guard_msgs in
def test7 (xs : List (Id Nat)) : List Nat := xs

-- Case 8: Id wrapping compound type
/--
warning: This code relies on the definitional equality `Id α = α`.

Note: This linter can be disabled with `set_option linter.warnOnUnfold false`
-/
#guard_msgs in
def test8 : Id (List Nat) := [1, 2, 3]

-- Case 9: Nat passed where Id Nat expected (via function parameter)
/--
warning: This code relies on the definitional equality `Id α = α`.

Note: This linter can be disabled with `set_option linter.warnOnUnfold false`
-/
#guard_msgs in
def test9 (f : Id Nat → Bool) (x : Nat) : Bool := f x

-- Case 10: Disabling the linter
#guard_msgs in
set_option linter.warnOnUnfold false in
def test10 (x : Id Nat) : Nat := x

-- Case 11: Id value used in IO context via `return` (warns correctly: Id Nat used as Nat)
/--
warning: This code relies on the definitional equality `Id α = α`.

Note: This linter can be disabled with `set_option linter.warnOnUnfold false`
-/
#guard_msgs in
def test11 : IO Nat := do
  let x : Id Nat := pure 42
  return x
