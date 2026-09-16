module
import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
/-! Native and kernel population count, including multi-limb results and BitVec clients. -/
example : Nat.popcount 0 = 0 := by decide +kernel
example : Nat.popcount 255 = 8 := by decide +kernel
example : Nat.popcount (2 ^ 256 - 1) = 256 := by decide +kernel
example : Nat.popcount (2 ^ 4096 + 2 ^ 64 + 1) = 3 := by decide +kernel
example : (0#0).cpop = 0#0 := by decide +kernel
example : (1#65536).cpop = 1#65536 := by decide +kernel
example : (511#9).cpop = 9#9 := by decide +kernel
example (x : BitVec 8) : x.cpop ≤ 8#8 := by bv_decide

example : Nat.popcount 255 = 8 := by decide
example : Nat.popcount 255 = 8 := rfl
example : Nat.popcount Nat.zero = 0 := rfl
example : Nat.popcount (Nat.succ 3) = 1 := rfl

-- Chunk endpoints, carry boundaries, and totals larger than a byte.
example : [247, 248, 249, 495, 496, 497].all (fun k =>
    Nat.popcount (2^k-1) == k && Nat.popcount (2^k) == 1) := by decide +kernel

example : True := by
  fail_if_success have : Nat.popcount 255 = 7 := by decide +kernel
  trivial
