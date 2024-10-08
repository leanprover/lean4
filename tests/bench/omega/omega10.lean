/-
time
1963
endtime
goal
case hsep.h.h₁.h.refine_4
s0 si : ArmState
h_si_x0_nonzero : si.x0 ≠ 0
h_s0_x1 : s0.x1 + 0x10#64 * (s0.x0 - si.x0) + 0x10#64 = s0.x1 + 0x10#64 * (s0.x0 - (si.x0 - 0x1#64))
h_s0_x2 : s0.x2 + 0x10#64 * (s0.x0 - si.x0) + 0x10#64 = s0.x2 + 0x10#64 * (s0.x0 - (si.x0 - 0x1#64))
h_assert_1 : si.x0 ≤ s0.x0
h_assert_3 : si.x1 = s0.x1 + 0x10#64 * (s0.x0 - si.x0)
h_assert_4 : si.x2 = s0.x2 + 0x10#64 * (s0.x0 - si.x0)
h_assert_6 :
  ∀ (n : Nat) (addr : BitVec 64),
    mem_separate' s0.x2 (0x10#64 * (s0.x0 - si.x0)).toNat addr n →
      Memory.read_bytes n addr si.mem = Memory.read_bytes n addr s0.mem
h_assert_5 :
  ∀ (i : BitVec 64),
    i < s0.x0 - si.x0 →
      Memory.read_bytes 16 (s0.x2 + 0x10#64 * i) si.mem = Memory.read_bytes 16 (s0.x1 + 0x10#64 * i) s0.mem
h_pre_1 : mem_separate' s0.x1 (s0.x0.toNat * 16) s0.x2 (s0.x0.toNat * 16)
n : Nat
addr : BitVec 64
hsep : mem_separate' s0.x2 (0x10#64 * (s0.x0 - (si.x0 - 0x1#64))).toNat addr n
h_le : (s0.x0 - (si.x0 - 0x1#64)).toNat ≤ s0.x0.toNat
h_upper_bound : addr.toNat + n ≤ 2 ^ 64
h_upper_bound₂ : s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64
h_upper_bound₃ : s0.x2.toNat + (0x10#64 * (s0.x0 - (si.x0 - 0x1#64))).toNat ≤ 2 ^ 64
h_width_lt : 0x10#64.toNat * (s0.x0 - (si.x0 - 0x1#64)).toNat < 2 ^ 64
⊢ (s0.x2 + 0x10#64 * (s0.x0 - si.x0)).toNat + 16 ≤ s0.x2.toNat + (0x10#64 * (s0.x0 - (si.x0 - 0x1#64))).toNat
endgoal

-/

