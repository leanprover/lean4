/-
time
1627
endtime
goal
case hsep.h.h₁.h.refine_3
-/


set_option maxHeartbeats 0 
set_option trace.profiler true 
set_option profiler true 
theorem foo
(h_si_x0_nonzero : six0 ≠ 0)
(h_s0_x1 : s0x1 + 0x10#64 * (s0x0 - six0) + 0x10#64 = s0x1 + 0x10#64 * (s0x0 - (six0 - 0x1#64)))
(h_s0_x2 : s0x2 + 0x10#64 * (s0x0 - six0) + 0x10#64 = s0x2 + 0x10#64 * (s0x0 - (six0 - 0x1#64)))
(h_assert_1 : six0 ≤ s0x0)
(h_assert_3 : six1 = s0x1 + 0x10#64 * (s0x0 - six0))
(h_assert_4 : six2 = s0x2 + 0x10#64 * (s0x0 - six0))
(n : Nat)
(addr : BitVec 64)
(h_le : (s0x0 - (six0 - 0x1#64)).toNat ≤ s0x0.toNat)
(h_upper_bound : addr.toNat + n ≤ 2 ^ 64)
(h_upper_bound₂ : s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64)
(h_upper_bound₃ : s0x2.toNat + (0x10#64 * (s0x0 - (six0 - 0x1#64))).toNat ≤ 2 ^ 64)
(h_width_lt : (0x10#64).toNat * (s0x0 - (six0 - 0x1#64)).toNat < 2 ^ 64)
: s0x2.toNat ≤ (s0x2 + 0x10#64 * (s0x0 - six0)).toNat := by bv_omega
