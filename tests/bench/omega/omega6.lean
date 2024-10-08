/-
time
1621
endtime
goal
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
h_pre_2 : r StateField.PC s0 = 0x8e0#64
h_pre_6 : 16 * s0.x0.toNat < 2 ^ 64
h_subset_2 : mem_subset' s0.x2 (0x10#64 * (s0.x0 - si.x0)).toNat s0.x2 (s0.x0.toNat * 16)
h_subset_1 : mem_subset' (s0.x1 + 0x10#64 * (s0.x0 - si.x0)) 16 s0.x1 (s0.x0.toNat * 16)
s2_sum_inbounds : s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64
hi : s0.x0 - si.x0 < s0.x0 - (si.x0 - 0x1#64)
i_sub_x0_mul_16 : 16 * (s0.x0 - si.x0).toNat < 16 * s0.x0.toNat
hmemSeparate_omega✝ : s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 ∧
  s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 ∧
    (s0.x1.toNat + s0.x0.toNat * 16 ≤ s0.x2.toNat ∨ s0.x1.toNat ≥ s0.x2.toNat + s0.x0.toNat * 16) :=
  cast
    (Eq.refl
      (s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 ∧
        s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 ∧
          (s0.x1.toNat + s0.x0.toNat * 16 ≤ s0.x2.toNat ∨ s0.x1.toNat ≥ s0.x2.toNat + s0.x0.toNat * 16)))
    (mem_separate'.omega_def h_pre_1)
hmemLegal_omega✝⁵ : s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 :=
  cast (Eq.refl (s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64)) (mem_legal'.omega_def h_pre_1.ha)
hmemLegal_omega✝⁴ : s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 :=
  cast (Eq.refl (s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64)) (mem_legal'.omega_def h_pre_1.hb)
hmemSubset_omega✝¹ : s0.x2.toNat + 16 % 2 ^ 64 * ((s0.x0.toNat + (2 ^ 64 - si.x0.toNat)) % 2 ^ 64) % 2 ^ 64 ≤ 2 ^ 64 ∧
  s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 ∧
    s0.x2.toNat + 16 % 2 ^ 64 * ((s0.x0.toNat + (2 ^ 64 - si.x0.toNat)) % 2 ^ 64) % 2 ^ 64 ≤
      s0.x2.toNat + s0.x0.toNat * 16 :=
  cast
    (congr
      (congrArg (fun x => And (s0.x2.toNat + x % 2 ^ 64 ≤ 2 ^ 64))
        (congr (congrArg HMul.hMul (BitVec.toNat_ofNat 16 64)) (BitVec.toNat_sub' s0.x0 si.x0)))
      (congrArg (And (s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64))
        (Eq.trans
          (congr (congrArg And (Arm.MinTheory._auxLemma.31 s0.x2.toNat))
            (congrArg (fun x => s0.x2.toNat + x % 2 ^ 64 ≤ s0.x2.toNat + s0.x0.toNat * 16)
              (congr (congrArg HMul.hMul (BitVec.toNat_ofNat 16 64)) (BitVec.toNat_sub' s0.x0 si.x0))))
          (true_and
            (s0.x2.toNat + 16 % 2 ^ 64 * ((s0.x0.toNat + (2 ^ 64 - si.x0.toNat)) % 2 ^ 64) % 2 ^ 64 ≤
              s0.x2.toNat + s0.x0.toNat * 16)))))
    (mem_subset'.omega_def h_subset_2)
hmemLegal_omega✝³ : s0.x2.toNat + 16 % 2 ^ 64 * ((s0.x0.toNat + (2 ^ 64 - si.x0.toNat)) % 2 ^ 64) % 2 ^ 64 ≤ 2 ^ 64 :=
  cast
    (congrArg (fun x => s0.x2.toNat + x % 2 ^ 64 ≤ 2 ^ 64)
      (congr (congrArg HMul.hMul (BitVec.toNat_ofNat 16 64)) (BitVec.toNat_sub' s0.x0 si.x0)))
    (mem_legal'.omega_def h_subset_2.ha)
hmemLegal_omega✝² : s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 :=
  cast (Eq.refl (s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64)) (mem_legal'.omega_def h_subset_2.hb)
hmemSubset_omega✝ : (s0.x1.toNat + 16 % 2 ^ 64 * ((s0.x0.toNat + (2 ^ 64 - si.x0.toNat)) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 +
      16 ≤
    2 ^ 64 ∧
  s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 ∧
    s0.x1.toNat ≤ (s0.x1.toNat + 16 % 2 ^ 64 * ((s0.x0.toNat + (2 ^ 64 - si.x0.toNat)) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 ∧
      (s0.x1.toNat + 16 % 2 ^ 64 * ((s0.x0.toNat + (2 ^ 64 - si.x0.toNat)) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 + 16 ≤
        s0.x1.toNat + s0.x0.toNat * 16 :=
  cast
    (congr
      (congrArg (fun x => And ((s0.x1.toNat + x % 2 ^ 64) % 2 ^ 64 + 16 ≤ 2 ^ 64))
        (congr (congrArg HMul.hMul (BitVec.toNat_ofNat 16 64)) (BitVec.toNat_sub' s0.x0 si.x0)))
      (congrArg (And (s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64))
        (congr
          (congrArg (fun x => And (s0.x1.toNat ≤ (s0.x1.toNat + x % 2 ^ 64) % 2 ^ 64))
            (congr (congrArg HMul.hMul (BitVec.toNat_ofNat 16 64)) (BitVec.toNat_sub' s0.x0 si.x0)))
          (congrArg (fun x => (s0.x1.toNat + x % 2 ^ 64) % 2 ^ 64 + 16 ≤ s0.x1.toNat + s0.x0.toNat * 16)
            (congr (congrArg HMul.hMul (BitVec.toNat_ofNat 16 64)) (BitVec.toNat_sub' s0.x0 si.x0))))))
    (mem_subset'.omega_def h_subset_1)
hmemLegal_omega✝¹ : (s0.x1.toNat + 16 % 2 ^ 64 * ((s0.x0.toNat + (2 ^ 64 - si.x0.toNat)) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 +
    16 ≤
  2 ^ 64 :=
  cast
    (congrArg (fun x => (s0.x1.toNat + x % 2 ^ 64) % 2 ^ 64 + 16 ≤ 2 ^ 64)
      (congr (congrArg HMul.hMul (BitVec.toNat_ofNat 16 64)) (BitVec.toNat_sub' s0.x0 si.x0)))
    (mem_legal'.omega_def h_subset_1.ha)
hmemLegal_omega✝ : s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 :=
  cast (Eq.refl (s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64)) (mem_legal'.omega_def h_subset_1.hb)
⊢ (s0.x2 + 0x10#64 * (s0.x0 - si.x0)).toNat + 16 ≤ 2 ^ 64 ∧
    (s0.x2 + 0x10#64 * (s0.x0 - si.x0)).toNat + 16 ≤ 2 ^ 64 ∧
      (s0.x2 + 0x10#64 * (s0.x0 - si.x0)).toNat ≤ (s0.x2 + 0x10#64 * (s0.x0 - si.x0)).toNat ∧
        (s0.x2 + 0x10#64 * (s0.x0 - si.x0)).toNat + 16 ≤ (s0.x2 + 0x10#64 * (s0.x0 - si.x0)).toNat + 16
endgoal
-/

