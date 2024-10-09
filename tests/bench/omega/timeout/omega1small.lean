-- We attempt to make subproblems out of `omega1`, both those where we remove redundant constraints
-- (to see if removing redundant constraints make omega faster),
-- and ones where we remove irredundant constraints (to see if omega can provide a counterexample quickly).
set_option profiler true 
theorem t
(six0 s0x0 : BitVec 64)
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



