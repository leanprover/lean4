import Lean.Util.Diff

open Lean.Diff

/-!
# Tests for diff

Tests for various parts of the diffing system
-/


/-!
## Prefix and Suffix Matching

These tests check that the prefix and suffix matching operations on subarrays used by diff perform
as expected.
-/

def Ex.abc' := #['a', 'b', 'c']
def Ex.abc := abc'.toSubarray

def Ex.abcde : Subarray Char := #['a','b','c','d','e'].toSubarray
def Ex.bcde : Subarray Char := #['b','c','d','e'].toSubarray

/-- info: (#['a', 'b', 'c'], #[].toSubarray, #['d', 'e'].toSubarray) -/
#guard_msgs in
#eval matchPrefix Ex.abc Ex.abcde

/-- info: (#['a', 'b', 'c'], #['d', 'e'].toSubarray, #[].toSubarray) -/
#guard_msgs in
#eval matchPrefix Ex.abcde Ex.abc

/-- info: (#[], #['a', 'b', 'c'].toSubarray, #['b', 'c', 'd', 'e'].toSubarray) -/
#guard_msgs in
#eval matchPrefix Ex.abc Ex.bcde

/-- info: (#[], #["A"].toSubarray, #["B"].toSubarray) -/
#guard_msgs in
#eval matchPrefix #["A"].toSubarray #["B"].toSubarray

/-- info: (#["D", "E", "F"], #["G"].toSubarray, #[].toSubarray) -/
#guard_msgs in
#eval matchPrefix #["D", "E", "F", "G"].toSubarray #["D", "E", "F"].toSubarray

/-- info: (#["A", "A"], #["B"].toSubarray, #["X"].toSubarray) -/
#guard_msgs in
#eval matchPrefix #["A", "A", "B"].toSubarray #["A", "A", "X"].toSubarray


def Ex.xyzabc : Subarray Char := #['x', 'y', 'z', 'a', 'b', 'c'].toSubarray
def Ex.xyzab : Subarray Char := #['x', 'y', 'z', 'a', 'b'].toSubarray

/-- info: (#[].toSubarray, #['x', 'y', 'z'].toSubarray, #['a', 'b', 'c']) -/
#guard_msgs in
#eval matchSuffix Ex.abc Ex.xyzabc

/-- info: (#['a', 'b', 'c'].toSubarray, #['x', 'y', 'z', 'a', 'b'].toSubarray, #[]) -/
#guard_msgs in
#eval matchSuffix Ex.abc Ex.xyzab

/-- info: (#['a'].toSubarray, #[].toSubarray, #['b']) -/
#guard_msgs in
#eval matchSuffix #['a', 'b'].toSubarray #['b'].toSubarray

/-!
## Least Common Subsequence

These tests find least common subsequences.
-/

/-- info: #[] -/
#guard_msgs in
#eval lcs (α := Nat) (#[].toSubarray) (#[].toSubarray)

/-- info: #[] -/
#guard_msgs in
#eval lcs  (#[1].toSubarray) (#[].toSubarray)

/-- info: #[1] -/
#guard_msgs in
#eval lcs  (#[1].toSubarray) (#[1].toSubarray)

/-- info: #[1, 3] -/
#guard_msgs in
#eval lcs  (#[1,3].toSubarray) (#[1,2,3].toSubarray)

/-- info: #["A", "A"] -/
#guard_msgs in
#eval lcs ("A,A,B".split (·==',') |>.toArray).toSubarray ("A,A,X".split (·==',') |>.toArray).toSubarray

/-- info: #["A", "D", "E", "F"] -/
#guard_msgs in
#eval lcs ("A,C,D,E,F,G".split (·==',') |>.toArray).toSubarray ("A,Y,Z,D,E,F".split (·==',') |>.toArray).toSubarray

/-- info: #["A", "A", "D", "E", "F"] -/
#guard_msgs in
#eval lcs ("A,A,B,C,D,E,F,G".split (·==',') |>.toArray).toSubarray ("A,A,X,Y,Z,D,E,F".split (·==',') |>.toArray).toSubarray
