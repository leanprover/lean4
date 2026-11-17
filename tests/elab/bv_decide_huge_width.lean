import Std.Tactic.BVDecide

/-!
The `bv_decide` normalizer does not evaluate bit-vector literals of width `2^32` or more.
Evaluating them requires computing `2^w`, and the runtime implementation of `Nat.pow` aborts the
process when the exponent does not fit in 32 bits.
For the same reason, `bv_decide` does not treat terms of such widths as bit-vector atoms.
-/

/--
error: unsolved goals
x : BitVec 4294967296
h✝ : x = 1#4294967296
x✝¹ : ¬x + x = 2#4294967296
h : (x == 1#4294967296) = true
x✝ : (!x + x == 2#4294967296) = true
⊢ False
-/
#guard_msgs in
example (x : BitVec 4294967296) (h : x = 1#4294967296) : x + x = 2#4294967296 := by
  bv_normalize

/--
error: unsolved goals
x : BitVec 4294967296
x✝¹ : ¬-1#4294967296 + x = x - 1#4294967296
x✝ : (!-1#4294967296 + x == x + -1#4294967296) = true
⊢ False
-/
#guard_msgs in
example (x : BitVec 4294967296) : (-1#4294967296) + x = x - 1#4294967296 := by
  bv_normalize

/--
error: unsolved goals
x : BitVec 8
h✝ : x = 1#8
x✝¹ : ¬x + x = 2#8
h : (x == 1#8) = true
x✝ : (!BitVec.extractLsb' 0 7 x ++ 0#1 == 2#8) = true
⊢ False
-/
#guard_msgs in
example (x : BitVec 8) (h : x = 1#8) : x + x = 2#8 := by
  bv_normalize

/--
error: The prover found a potentially spurious counterexample:
- It abstracted the following unsupported expressions as opaque variables:
  - 1#8 ++ 0#4294967296 == x
Consider the following assignment:
1#8 ++ 0#4294967296 == x = false
-/
#guard_msgs in
example (x : BitVec (8 + 4294967296)) : 1#8 ++ 0#4294967296 = x := by
  bv_decide

/--
error: The prover found a potentially spurious counterexample:
- It abstracted the following unsupported expressions as opaque variables:
  - x == y
Consider the following assignment:
x == y = false
-/
#guard_msgs in
example (x y : BitVec 4294967296) : x = y := by
  bv_decide
