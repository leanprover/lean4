module
example {n} (x y : BitVec n) : x * y = y * x := by
  grind

example {n} (x y z w : BitVec n) : w = z → x * y - z*w = 0 → z*z = y * x := by
  grind

example (x y : BitVec 64) : x * y = y * x := by
  grind

example (x y : BitVec 128) : x * y = y * x := by
  grind

example (x y : BitVec 128) : x * y = y * x + 2^64 * 2^64 * x := by
  grind

example (x y : BitVec 256) : x * y = y * x := by
  grind

example (x y : BitVec 1024) : x * y = y * x := by
  grind

example (x y : BitVec 1024) : x * y = y * x := by
  grind -lia

example (x y : BitVec 100000) : x * y = y * x := by
  grind -lia

example (x y z : BitVec 100000) : x * y - z*z = 0 → z*z = y * x := by
  grind -lia

/--
trace: [grind.issues] exponent 1024 exceeds threshold for exponentiation `(exp := 16)`
[grind.issues] exponent 1024 exceeds threshold for exponentiation `(exp := 16)`
-/
#guard_msgs in
set_option trace.grind.issues true in
example (x y : BitVec 1024) : x * y = y * x := by
  grind (exp := 16)
