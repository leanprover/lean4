/-
tactic execution of Lean.Parser.Tactic.omega took 6.04s
instantiate metavars took 31.6s
share common exprs took 5.61s
type checking took 1.36s
process pre-definitions took 1.02s
-/
set_option maxHeartbeats 0 
set_option trace.profiler true 
set_option profiler true 
theorem memcpy_extracted_2 (six0 s0x0 : BitVec 64)
(h_six0_nonzero : six0 ≠ 0)
(h_s0x1 : s0x1 + 16#64 * (s0x0 - six0) + 16#64 = s0x1 + 16#64 * (s0x0 - (six0 - 1#64)))
(h_s0x2 : s0x2 + 16#64 * (s0x0 - six0) + 16#64 = s0x2 + 16#64 * (s0x0 - (six0 - 1#64)))
(h_assert_1 : six0 ≤ s0x0)
(h_assert_3 : six1 = s0x1 + 16#64 * (s0x0 - six0))
(h_assert_4 : six2 = s0x2 + 16#64 * (s0x0 - six0))
(n : Nat)
(addr : BitVec 64)
(h_le : (s0x0 - (six0 - 1#64)).toNat ≤ s0x0.toNat)
(h_upper_bound : addr.toNat + n ≤ 2 ^ 64)
(h_upper_bound₂ : s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64)
(h_upper_bound₃ : s0x2.toNat + (16#64 * (s0x0 - (six0 - 1#64))).toNat ≤ 2 ^ 64)
(h_width_lt : (16#64).toNat * (s0x0 - (six0 - 1#64)).toNat < 2 ^ 64)
(hmemSeparate_omega : s0x1.toNat + s0x0.toNat * 16 ≤ 2 ^ 64 ∧
  s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64 ∧
    (s0x1.toNat + s0x0.toNat * 16 ≤ s0x2.toNat ∨ s0x1.toNat ≥ s0x2.toNat + s0x0.toNat * 16))
(hmemLegal_omega : s0x1.toNat + s0x0.toNat * 16 ≤ 2 ^ 64)
(hmemLegal_omega : s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64)
(hmemSeparate_omega : s0x2.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - (2 ^ 64 - 1 % 2 ^ 64 + six0.toNat) % 2 ^ 64 + s0x0.toNat) % 2 ^ 64) % 2 ^ 64 ≤
    2 ^ 64 ∧
  addr.toNat + n ≤ 2 ^ 64 ∧
    (s0x2.toNat +
          16 % 2 ^ 64 * ((2 ^ 64 - (2 ^ 64 - 1 % 2 ^ 64 + six0.toNat) % 2 ^ 64 + s0x0.toNat) % 2 ^ 64) % 2 ^ 64 ≤
        addr.toNat ∨
      s0x2.toNat ≥ addr.toNat + n))
(hmemLegal_omega : s0x2.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - (2 ^ 64 - 1 % 2 ^ 64 + six0.toNat) % 2 ^ 64 + s0x0.toNat) % 2 ^ 64) % 2 ^ 64 ≤
  2 ^ 64)
(hmemLegal_omega : addr.toNat + n ≤ 2 ^ 64) :
 s0x2.toNat + (16#64 * (s0x0 - six0)).toNat ≤ 2 ^ 64 ∧
  addr.toNat + n ≤ 2 ^ 64 ∧
    (s0x2.toNat + (16#64 * (s0x0 - six0)).toNat ≤ addr.toNat ∨ s0x2.toNat ≥ addr.toNat + n) := by
    bv_omega


