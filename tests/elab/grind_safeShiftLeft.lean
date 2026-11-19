/-!
`grind` does not evaluate left shifts of literals whose shift amount is above the
`shiftLeft.threshold` option. The runtime implementation of `Nat.shiftLeft` aborts the process
when the shift amount does not fit in 32 bits (#15193).
-/

/--
warning: shift amount 4294967296 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : Nat) (h : x = 4294967296) : (1 <<< x : Nat) = 0 := by grind

/--
warning: shift amount 4294967296 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example : (1 <<< 4294967296 : Nat) = 0 := by grind

/--
warning: shift amount 4294967296 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y : BitVec 8) (n : Nat) (h : n = 4294967296) (hx : x = 1#8) : x <<< n = y := by grind

/--
warning: shift amount 4294967296 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y : BitVec 8) (n : Nat) (h : n = 4294967296) (hx : x = 1#8) : x.shiftLeft n = y := by grind

/--
warning: shift amount 4294967296 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y : BitVec 8) (n : BitVec 64) (h : n = 4294967296#64) (hx : x = 1#8) : x <<< n = y := by grind

#guard_msgs in
example (x y : Nat) (h : x = 4294967296) (hy : y = 0) (f : Nat → Nat) : f (y <<< x) = f 0 := by grind

/--
warning: shift amount 4294967296 does not fit in 32 bits, left shift operation was not evaluated
---
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
set_option shiftLeft.threshold 5000000000 in
example (x : Nat) (h : x = 4294967296) : (1 <<< x : Nat) = 0 := by grind

#guard_msgs in
example (x : Nat) (h : x = 10) : (1 <<< x : Nat) = 1024 := by grind

#guard_msgs in
example (x : Nat) (h : x = 65536) : (1 <<< x : Nat) % 2 = 0 := by grind

#guard_msgs in
example (x : BitVec 8) (n : Nat) (h : n = 3) (hx : x = 1#8) : x <<< n = 8#8 := by grind

#guard_msgs in
example (x : BitVec 8) (n : Nat) (h : n = 3) (hx : x = 1#8) : x.shiftLeft n = 8#8 := by grind

#guard_msgs in
example (x : BitVec 8) (n : BitVec 8) (h : n = 3#8) (hx : x = 1#8) : x <<< n = 8#8 := by grind

/--
warning: shift amount 10 exceeds the threshold 2, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
-/
#guard_msgs in
set_option shiftLeft.threshold 2 in
example (x y : Nat) (h : x = 10) (hy : y = 3) (f : Nat → Nat) : f (y <<< x) = f 3072 := by grind

#guard_msgs in
example (x y : Nat) (h : x = 10) (hy : y = 3) (f : Nat → Nat) : f (y <<< x) = f 3072 := by grind

/--
warning: shift amount 3 exceeds the threshold 2, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
set_option shiftLeft.threshold 2 in
example (x : BitVec 8) (y : BitVec 8) (n : Nat) (h : n = 3) (hx : x = 1#8) : x <<< n = y := by grind
