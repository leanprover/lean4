/-!
# Test for warning when `Where` (capitalized) is used instead of `where`

Relates to: https://github.com/leanprover/lean4/issues/11853
-/

-- Test that `Where` in inductive is accepted but generates a warning
/--
warning: `Where` should be lowercase `where`
-/
#guard_msgs in
inductive MyResult (α : Type) : Type Where
  | Ok : α → MyResult α
  | Err : String → MyResult α

-- Verify the inductive works correctly
#check MyResult.Ok
#check MyResult.Err

-- Test that `Where` in structure is accepted but generates a warning
/--
warning: `Where` should be lowercase `where`
-/
#guard_msgs in
structure MyPoint Where
  x : Nat
  y : Nat

-- Verify the structure works correctly
#check MyPoint.mk
#check MyPoint.x

-- Test that lowercase `where` does not generate a warning
inductive MyResult2 (α : Type) : Type where
  | Ok : α → MyResult2 α
  | Err : String → MyResult2 α

structure MyPoint2 where
  x : Nat
  y : Nat
