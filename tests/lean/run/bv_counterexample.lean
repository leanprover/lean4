import Std.Tactic.BVDecide

open BitVec

/--
error: The prover found a counterexample, consider the following assignment:
x = 0xffffffffffffffff#64
-/
#guard_msgs in
example (x : BitVec 64) : x < x + 1 := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
x = 0x00000000000001ff#64
-/
#guard_msgs in
example (x : BitVec 64) (h : x < 512) : x ^^^ x ≠ 0 := by
  bv_decide


/-
This is a modified version of Eval.Popcount with a mistake
-/

def pop_spec' (x : BitVec 32) : BitVec 32 :=
  go x 0 32
where
  go (x : BitVec 32) (pop : BitVec 32) (i : Nat) : BitVec 32 :=
    match i with
    | 0 => pop
    | i + 1 =>
      let pop := pop + (x &&& 1)
      go (x >>> 1) pop i

def optimized (x : BitVec 32) : BitVec 32 :=
    let x := x - ((x >>> 1) &&& 0x55555555);
    let x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333);
    let x := (x + (x >>> 4)) &&& 0x0F0F0F0F;
    let x := x + (x >>> 8);
    let x := x + (x >>> 16);
    -- MISTAKE HERE: the 4 should be a 3
    x &&& 0x0000004F

/--
error: The prover found a counterexample, consider the following assignment:
x = 0xffffffff#32
-/
#guard_msgs in
example (x : BitVec 32) : pop_spec' x = optimized x := by
  dsimp [pop_spec', pop_spec'.go, optimized]
  bv_decide

-- limit the search domain
/--
error: The prover found a counterexample, consider the following assignment:
x = 0x0007ffff#32
-/
#guard_msgs in
example (x : BitVec 32) (h1 : x < 0xfffff) : pop_spec' x = optimized x := by
  dsimp [pop_spec', pop_spec'.go, optimized]
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
x = 0x00000000#32
y = 0x80000000#32
ofBool a = 0x1#1
-/
#guard_msgs in
example (x y : BitVec 32) (a : Bool) (h : x < y) : (x = y) ↔ a := by
  bv_decide

-- False counter examples but correctly detected as such.
/--
error: The prover found a potentially spurious counterexample:
- The following potentially relevant hypotheses could not be used: [h]
Consider the following assignment:
x = 0xffffffff#32
y = 0x7fffffff#32
-/
#guard_msgs in
example (x y : BitVec 32) (h : x.toNat = y.toNat) : x = y := by
  bv_decide

def zeros (w : Nat) : BitVec w := 0#w

/--
error: The prover found a potentially spurious counterexample:
- It abstracted the following unsupported expressions as opaque variables: [zeros 32]
Consider the following assignment:
x = 0xffffffff#32
zeros 32 = 0xffffffff#32
-/
#guard_msgs in
example (x : BitVec 32) (h : x = zeros 32) : x = 0 := by
  bv_decide

/--
error: The prover found a potentially spurious counterexample:
- It abstracted the following unsupported expressions as opaque variables: [zeros 32]
- The following potentially relevant hypotheses could not be used: [h1]
Consider the following assignment:
x = 0xffffffff#32
zeros 32 = 0xffffffff#32
y = 0xffffffff#32
-/
#guard_msgs in
example (x y : BitVec 32) (h1 : x.toNat = y.toNat) (h2 : x = zeros 32) : y = 0 := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
x = 0x3#2
-/
#guard_msgs in
example (x : BitVec 2) : (bif x.ult 0#2 then 1#2 else 2#2) == 3#2 := by
  bv_decide
