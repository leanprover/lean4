import Std.Tactic.BVDecide

/-!
Test for `bv_decide` in `sym =>` mode.
-/

def optimized (x : BitVec 32) : BitVec 32 :=
  let x := x - ((x >>> 1) &&& 0x55555555);
  let x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333);
  let x := (x + (x >>> 4)) &&& 0x0F0F0F0F;
  let x := x + (x >>> 8);
  let x := x + (x >>> 16);
  x &&& 0x0000003F

example : optimized x = BitVec.cpop x := by
  sym =>
    simp [optimized.eq_def]
    bv_decide

example {x : BitVec 16} : x + 1 - 1 = x := by
  sym =>
    bv_normalize

/-- error: tactic is only available in `sym =>` mode -/
#guard_msgs in
example {x : BitVec 16} : x + 1 - 1 = x := by
  grind =>
    bv_normalize
