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
(h_pre_6 : 16 * s0x0.toNat < 2 ^ 64)
(s2_sum_inbounds : s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64)
(hi : s0x0 - six0 < s0x0 - (six0 - 0x1#64))
(i_sub_x0_mul_16 : 16 * (s0x0 - six0).toNat < 16 * s0x0.toNat)
(hmemSeparate_omega : s0x1.toNat + s0x0.toNat * 16 ≤ 2 ^ 64 ∧
  s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64 ∧
    (s0x1.toNat + s0x0.toNat * 16 ≤ s0x2.toNat ∨ s0x1.toNat ≥ s0x2.toNat + s0x0.toNat * 16))
(hmemLegal_omega: s0x1.toNat + s0x0.toNat * 16 ≤ 2 ^ 64)
(hmemLegal_omega : s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64)
(hmemSubset_omega : s0x2.toNat + 16 % 2 ^ 64 * ((s0x0.toNat + (2 ^ 64 - six0.toNat)) % 2 ^ 64) % 2 ^ 64 ≤ 2 ^ 64 ∧
  s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64 ∧
    s0x2.toNat + 16 % 2 ^ 64 * ((s0x0.toNat + (2 ^ 64 - six0.toNat)) % 2 ^ 64) % 2 ^ 64 ≤
      s0x2.toNat + s0x0.toNat * 16)
(hmemLegal_omega : s0x2.toNat + 16 % 2 ^ 64 * ((s0x0.toNat + (2 ^ 64 - six0.toNat)) % 2 ^ 64) % 2 ^ 64 ≤ 2 ^ 64)
(hmemLegal_omega : s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64 )
(hmemSubset_omega : (s0x1.toNat + 16 % 2 ^ 64 * ((s0x0.toNat + (2 ^ 64 - six0.toNat)) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 +
      16 ≤
    2 ^ 64 ∧
  s0x1.toNat + s0x0.toNat * 16 ≤ 2 ^ 64 ∧
    s0x1.toNat ≤ (s0x1.toNat + 16 % 2 ^ 64 * ((s0x0.toNat + (2 ^ 64 - six0.toNat)) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 ∧
      (s0x1.toNat + 16 % 2 ^ 64 * ((s0x0.toNat + (2 ^ 64 - six0.toNat)) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 + 16 ≤
        s0x1.toNat + s0x0.toNat * 16)
(hmemLegal_omega : (s0x1.toNat + 16 % 2 ^ 64 * ((s0x0.toNat + (2 ^ 64 - six0.toNat)) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 +
    16 ≤
  2 ^ 64)
(hmemLegal_omega : s0x1.toNat + s0x0.toNat * 16 ≤ 2 ^ 64 )
: (s0x2 + 0x10#64 * (s0x0 - six0)).toNat + 16 ≤ 2 ^ 64 ∧
    (s0x2 + 0x10#64 * (s0x0 - six0)).toNat + 16 ≤ 2 ^ 64 ∧
      (s0x2 + 0x10#64 * (s0x0 - six0)).toNat ≤ (s0x2 + 0x10#64 * (s0x0 - six0)).toNat ∧
        (s0x2 + 0x10#64 * (s0x0 - six0)).toNat + 16 ≤ (s0x2 + 0x10#64 * (s0x0 - six0)).toNat + 16 := by bv_omega

