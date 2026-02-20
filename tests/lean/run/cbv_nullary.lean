set_option cbv.warning false

/-! Tests for `cbv` evaluation of nullary (non-function) constants.

Nullary definitions like `def myNat : Nat := 42` should be unfolded by `cbv`
so that ground term evaluation (e.g. `evalEq`, `evalLT`) can recognize their
values as literals.
-/

def myNat : Nat := 42

-- Arithmetic: argument goes through pattern matching in Nat.add
example : myNat + 1 = 43 := by cbv

-- Direct equality
example : myNat = 42 := by cbv

-- Prop-level equality and comparisons
example : (myNat = myNat) = True := by cbv
example : (myNat = 42) = True := by cbv
example : (myNat < 100) = True := by cbv
example : (myNat ≤ 42) = True := by cbv

-- Bool-level equality
example : (myNat == 42) = true := by cbv

-- Condition involving a nullary constant
example : (if myNat = 42 then 1 else 0) = 1 := by cbv

-- String nullary constant
def myStr : String := "hello"

example : myStr.length = 5 := by cbv
example : (myStr = "hello") = True := by cbv

-- Custom inductive type
inductive Color where | red | green | blue

def myColor : Color := .red

def colorToNat : Color → Nat
  | .red => 1
  | .green => 2
  | .blue => 3

example : colorToNat myColor = 1 := by cbv
