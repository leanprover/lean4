/-!
Bit-vector literals of width `2^32` or more are not evaluated by `simp` and `cbv`.
Evaluating them requires computing `2^w`, and the runtime implementation of `Nat.pow` aborts the
process when the exponent does not fit in 32 bits.
-/

-- `simp`

/--
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : 1#4294967296 = x := by simp

/--
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ 5#4294967296 = x
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (5 : BitVec 4294967296) = x := by simp

/--
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : 1#4294967296 + 1#4294967296 = x := by simp

/--
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : -1#4294967296 = x := by simp

/--
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : ~~~1#4294967296 = x := by simp

/--
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ 3#4294967296 = x
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : 1#4294967296 * 3#4294967296 = x := by simp

/--
warning: exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ 1 = n
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (1#4294967296).toNat = n := by simp

/--
warning: exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ 1 = n
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.setWidth 4294967296 1#8).toNat = n := by simp

/--
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.signExtend 4294967296 255#8).toNat = n := by simp

/--
warning: exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ (-1 % 2 ^ 4294967296).toNat = n
---
error: (kernel) the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.ofInt 4294967296 (-1)).toNat = n := by simp

/--
warning: exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ 2 ^ 4294967296 - 1 = n
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.allOnes 4294967296).toNat = n := by simp

/--
error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.replicate 4294967296 1#1).toNat = n := by simp

/--
warning: exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ 1 = n
---
error: (kernel) the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.extractLsb' 0 4294967296 1#8).toNat = n := by simp

/--
warning: exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ 0 = n
---
error: (kernel) the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.extractLsb 4294967296 1 1#8).toNat = n := by simp

/--
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.ofNatClamp 4294967296 5).toNat = n := by simp

/--
warning: exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ 5 % 2 ^ 4294967296 = n
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.ofNat 4294967296 (2 + 3)).toNat = n := by simp

/--
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ 1 = n
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.setWidth 8 1#4294967296).toNat = n := by simp

/--
warning: exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: unsolved goals
⊢ 1 < 2 % 2 ^ 4294967296
-/
#guard_msgs in
example : 1#4294967296 < 2#4294967296 := by simp

-- `cbv`

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : 1#4294967296 = x := by cbv

/--
warning: exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (5 : BitVec 4294967296) = x := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : 1#4294967296 + 1#4294967296 = x := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : -1#4294967296 = x := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : ~~~1#4294967296 = x := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : 1#4294967296 * 3#4294967296 = x := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (1#4294967296).toNat = n := by cbv

/--
error: unsolved goals
x : BitVec 4294967296
n : Nat
⊢ 1 = n
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.setWidth 4294967296 1#8).toNat = n := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.signExtend 4294967296 255#8).toNat = n := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.ofInt 4294967296 (-1)).toNat = n := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.allOnes 4294967296).toNat = n := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.extractLsb' 0 4294967296 1#8).toNat = n := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.extractLsb 4294967296 1 1#8).toNat = n := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.ofNatClamp 4294967296 5).toNat = n := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.ofNat 4294967296 (2 + 3)).toNat = n := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.setWidth 8 1#4294967296).toNat = n := by cbv

-- Bit-vectors of regular widths are still evaluated.

#guard_msgs in
example : 255#8 + 1#8 = 0#8 := by simp

#guard_msgs in
example : 255#8 + 1#8 = 0#8 := by cbv

#guard_msgs in
example : BitVec.setWidth 16 255#8 = 255#16 := by simp

#guard_msgs in
example : BitVec.setWidth 16 255#8 = 255#16 := by cbv

#guard_msgs in
example : BitVec.allOnes 8 = 255#8 := by simp

#guard_msgs in
example : BitVec.replicate 2 1#4 = 17#8 := by cbv
