/-!
`grind` does not evaluate bit-vector literals of width `2^32` or more (#15786).
Evaluating them requires computing `2^w`, and the runtime implementation of `Nat.pow` aborts the
process when the exponent does not fit in 32 bits.
-/

-- #15786

#guard_msgs in
example (x y : BitVec 4294967296) (h : x = y) : y = x := by
  grind

#guard_msgs in
example (x : BitVec 4294967296) (h : x = 5) : x = 5 := by
  grind

#guard_msgs in
example (x : BitVec (2 ^ 32)) (h : x = 5) : x = 5 := by
  grind

#guard_msgs in
example (x : BitVec 4294967296) (h : x = 1#4294967296) : x = 1#4294967296 := by
  grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : 1#4294967296 = x := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (5 : BitVec 4294967296) = x := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : 1#4294967296 + 1#4294967296 = x := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : -1#4294967296 = x := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : ~~~1#4294967296 = x := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : 1#4294967296 * 3#4294967296 = x := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (1#4294967296).toNat = n := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.setWidth 4294967296 1#8).toNat = n := by grind

/--
warning: exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold
---
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.signExtend 4294967296 255#8).toNat = n := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.ofInt 4294967296 (-1)).toNat = n := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.allOnes 4294967296).toNat = n := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.replicate 4294967296 1#1).toNat = n := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.extractLsb' 0 4294967296 1#8).toNat = n := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.extractLsb 4294967296 1 1#8).toNat = n := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.ofNatClamp 4294967296 5).toNat = n := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.ofNat 4294967296 (2 + 3)).toNat = n := by grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : BitVec 4294967296) (n : Nat) : (BitVec.setWidth 8 1#4294967296).toNat = n := by grind

#guard_msgs in
example (x : BitVec 8) (h : x = 255#8) : x + 1#8 = 0#8 := by grind

#guard_msgs in
example (x : BitVec 8) (h : x = 255#8) : BitVec.setWidth 16 x = 255#16 := by grind
