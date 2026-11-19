/-!
Exponents that do not fit in 32 bits are not evaluated, even if `exponentiation.threshold` is
increased. The runtime implementation of `Nat.pow` aborts the process on them.
-/

/--
warning: exponent 4294967296 does not fit in 32 bits, exponentiation operation was not evaluated
---
error: `simp` made no progress
-/
#guard_msgs in
set_option exponentiation.threshold 5000000000 in
example (x : Nat) : 2 ^ 4294967296 = x := by simp

/--
warning: exponent 4294967296 does not fit in 32 bits, exponentiation operation was not evaluated
---
error: `simp` made no progress
-/
#guard_msgs in
set_option exponentiation.threshold 5000000000 in
example (x : Int) : (2 : Int) ^ 4294967296 = x := by simp

/--
warning: exponent 4294967296 does not fit in 32 bits, exponentiation operation was not evaluated
---
error: `simp` made no progress
-/
#guard_msgs in
set_option exponentiation.threshold 5000000000 in
example (x : Int) : (-2 : Int) ^ 4294967296 = x := by simp

/--
warning: exponent 4294967296 does not fit in 32 bits, exponentiation operation was not evaluated
---
error: `simp` made no progress
-/
#guard_msgs in
set_option exponentiation.threshold 5000000000 in
example (x : Nat) : Nat.powMod 2 4294967296 0 = x := by simp

/--
warning: exponent 4294967296 does not fit in 32 bits, exponentiation operation was not evaluated
---
error: `simp` made no progress
-/
#guard_msgs in
set_option exponentiation.threshold 5000000000 in
example (x : Nat) : x % 2 ^ 4294967296 = x := by simp

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
set_option exponentiation.threshold 5000000000 in
example (x : Nat) : 2 ^ 4294967296 = x := by grind

/--
error: `lia` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
set_option exponentiation.threshold 5000000000 in
example (x : Nat) : x % 2 ^ 4294967296 = x := by lia

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
set_option exponentiation.threshold 5000000000 in
example (x : Rat) : (2 : Rat) ^ (-4294967296 : Int) = x := by grind

#guard_msgs in
set_option exponentiation.threshold 5000 in
example : 2 ^ 5000 % 2 = 0 := by simp

#guard_msgs in
set_option exponentiation.threshold 5000 in
example : 2 ^ 5000 % 2 = 0 := by rfl
