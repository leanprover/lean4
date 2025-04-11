set_option grind.warning false
set_option grind.debug true
open Int.Linear

set_option trace.grind.cutsat.assert true

/--
info: [grind.cutsat.assert] a + b + 1 ≤ 0
[grind.cutsat.assert] a + -1*b ≠ 0
-/
#guard_msgs (info) in
example (a b : Int) : a + b < 0 → a ≠ b → False := by
  (fail_if_success grind); sorry

#guard_msgs (info) in -- `a` and `b` are not relevant to cutsat in the following example
example (a b : Int) : a ≠ b → False := by
  (fail_if_success grind); sorry

/--
info: [grind.cutsat.assert] a + -1*b ≠ 0
[grind.cutsat.assert] a + b + 1 ≤ 0
-/
#guard_msgs (info) in
example (a b : Int) : a ≠ b → a + b < 0 → False := by
  (fail_if_success grind); sorry

/--
info: [grind.cutsat.assert] a + -1*b ≠ 0
[grind.cutsat.assert] a + b + 1 ≤ 0
-/
#guard_msgs (info) in
example (a b c : Int) : a ≠ c → c = b → a + b < 0 → False := by
  (fail_if_success grind); sorry

/--
info: [grind.cutsat.assert] a + -1*b ≠ 0
[grind.cutsat.assert] a + b + 1 ≤ 0
-/
#guard_msgs (info) in
example (a b c d : Int) : d ≠ c → c = b → a = d → a + b < 0 → False := by
  (fail_if_success grind); sorry

/--
info: [grind.cutsat.assert] a + b + 1 ≤ 0
[grind.cutsat.assert] a + -1*b ≠ 0
-/
#guard_msgs (info) in
example (a b c d : Int) : d ≠ c → a = d → a + b < 0 → c = b → False := by
  (fail_if_success grind); sorry

/--
info: [grind.cutsat.assert] a + b + 1 ≤ 0
[grind.cutsat.assert] a + -1*b ≠ 0
[grind.cutsat.assert] e + -1*b = 0
[grind.cutsat.assert] -1*e + 1 ≤ 0
-/
#guard_msgs (info) in
example (a b c d e : Int) : d ≠ c → a = d → a + b < 0 → c = b → c = e → e > 0 → False := by
  (fail_if_success grind); sorry

/--
info: [grind.cutsat.assert] -1*e + 1 ≤ 0
[grind.cutsat.assert] b + -1*e = 0
[grind.cutsat.assert] a + -1*e ≠ 0
[grind.cutsat.assert] a + b + 1 ≤ 0
-/
#guard_msgs (info) in
example (a b c d e : Int) : d ≠ c → a = d → c = b → c = e → e > 0 → a + b < 0 → False := by
  (fail_if_success grind); sorry

/--
info: [grind.cutsat.assert] -1*e + 1 ≤ 0
[grind.cutsat.assert] b + -1*e = 0
[grind.cutsat.assert] a + b + 1 ≤ 0
[grind.cutsat.assert] a + -1*e ≠ 0
-/
#guard_msgs (info) in
example (a b c d e : Int) : a = d → c = b → c = e → e > 0 → a + b < 0 → d ≠ c → False := by
  (fail_if_success grind); sorry

#guard_msgs (info) in -- no propagation to cutsat
example (a b c d e : Int) : a = d → c = b → c = e → a = 1 → d ≠ c → False := by
  (fail_if_success grind); sorry

example (a b c : Int) : a + 2*b = 0 → c + b = -b → a = c := by
  grind

example (a b c : Int) : a + 2*b = 0 → a = c → c + b = -b := by
  grind
