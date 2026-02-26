/-!
# Tests of `pp.oneline`

These tests are only making sure that `pp.online` renders correctly as a string.
There is also logic to preserve tags that is not being tested.
-/

set_option pp.oneline true

/-!
Prints something that fits in one line normally.
-/
/-- info: 1 + 1 : Nat -/
#guard_msgs in #check 1 + 1

/-!
Setting the width to 10 characters, truncates.
-/
/-- info: [1, 2, 3, [...] : List Nat -/
#guard_msgs in set_option format.width 10 in #check [1,2,3,4,5,6,7,8,9,10]

/-!
`let` prints across two lines, so truncates.
-/
/-- info: let x := 1; [...] : Nat -/
#guard_msgs in #check let x := 1; x + x

/-!
Doesn't truncate mid-token, but does truncate without regard for semantic position.
-/
/-- info: fun x1 [...] : Nat → [...] -/
#guard_msgs in set_option format.width 8 in #check fun x1 x2 x3 => (x1 + x2 + x3 : Nat)
/-- info: fun x1 x2 [...] : Nat → [...] -/
#guard_msgs in set_option format.width 9 in #check fun x1 x2 x3 => (x1 + x2 + x3 : Nat)
/-- info: fun x1 x2 [...] : Nat → [...] -/
#guard_msgs in set_option format.width 14 in #check fun x1 x2 x3 => (x1 + x2 + x3 : Nat)
/-- info: fun x1 x2 x3 => [...] : Nat → [...] -/
#guard_msgs in set_option format.width 15 in #check fun x1 x2 x3 => (x1 + x2 + x3 : Nat)
