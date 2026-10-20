import Std.Tactic.BVDecide

/-!
Tests for `bv_decide_push`, the incremental pre-processor for `bv_decide` in `sym =>` and `grind =>`
mode. It hands the caches of the `bv_normalize` passes to the pre-processor runs that follow it on
the same goal, so a goal preceded by a `bv_decide_push` has to be solved exactly like it would be
without one.
-/

opaque st : BitVec 64

structure Pair where
  a : BitVec 32
  b : BitVec 32

example (x y : BitVec 64) (h : x = y + 1#64) : x - 1#64 = y := by
  sym =>
    bv_decide_push
    bv_decide

example (x y : BitVec 64) (h : x = y + 1#64) : x - 1#64 = y := by
  sym =>
    bv_decide_push
    bv_decide_push
    bv_decide

example (x : BitVec 64) (h : x = 1#64 ∨ x = 2#64) : x &&& 3#64 = x := by
  sym =>
    bv_decide_push
    cases_next
    all_goals bv_decide

example (p : Pair) (h : p.a = 0#32) : p.a &&& p.b = 0#32 := by
  sym =>
    bv_decide_push
    bv_decide

example : (st &&& 0xff00#64) ||| (st &&& 0xffffffffffff00ff#64) = st := by
  grind =>
    bv_decide_push
    bv_decide

example (x : BitVec 8) (h : x &&& 0#8 = 1#8) : x = x + 1 := by
  sym =>
    bv_decide_push

/-- error: No goals to be solved -/
#guard_msgs in
example (x : BitVec 8) (h : x &&& 0#8 = 1#8) : x = x + 1 := by
  sym =>
    bv_decide_push
    bv_decide
