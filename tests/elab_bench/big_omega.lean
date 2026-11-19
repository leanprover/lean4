/-!
This benchmark exercises `omega` in a way that creates a big proof, exercising `instantiateMVars`
and `shareCommonPreDefs` as well. In particular, running it with `internal.cmdlineSnapshots=false`,
like the language server does, uncovered a significant slowdown in `instantiateMVars` (#5614).
-/

set_option maxHeartbeats 0
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
