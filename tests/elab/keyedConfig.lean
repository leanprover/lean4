module

import all Lean.Meta.Basic

/-!
This file proves that optimized bit-fiddling operations on WHNF config keys are correct.
-/

open Lean Meta

/-!
# Preparations
-/

/--
A term shifted left by `k` (with `3 ≤ k < 64`) is unchanged by `>>> 3 <<< 3`
(its bits all sit at position ≥ 3, so clearing the low 3 bits is a no-op).
-/
theorem shiftLeft_shiftRight_shiftLeft_of_three_le (x k : UInt64) (hk3 : 3 ≤ k.toNat) (hk64 : k.toNat < 64) :
    (x <<< k) >>> (3:UInt64) <<< 3 = x <<< k := by
  apply UInt64.toBitVec_inj.1
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro i hi
  have hkn : (k.toBitVec % 64).toNat = k.toNat := by
    rw [BitVec.toNat_umod]; exact Nat.mod_eq_of_lt hk64
  simp only [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
             BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
             BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
             show (UInt64.toBitVec 3 % 64).toNat = 3 from by decide, hkn]
  rw [show 3 + (i - 3) - k.toNat = i - k.toNat from by omega]
  rcases Nat.lt_or_ge i 3 with h|h <;> rcases Nat.lt_or_ge i k.toNat with h'|h' <;>
    simp_all <;> omega

/-!
# Proofs
-/

example (c : ConfigWithKey) (h : c.config.toKey = c.key) :
    let c' := c.withCanUnfoldAtMatcherPred
    c'.config.toKey = c'.key := by
  obtain ⟨cfg, k⟩ := c
  simp only [ConfigWithKey.withCanUnfoldAtMatcherPred] at h ⊢
  subst h
  simp only [Config.toKey, CanUnfoldPredicateConfig.atMatcher]
  cases cfg.canUnfoldPredicateConfig.toBool <;>
    simp [Bool.toUInt64, UInt64.or_assoc, UInt64.or_self, UInt64.or_zero]

example (c : ConfigWithKey) (t : TransparencyMode) (h : c.config.toKey = c.key) :
    let c' := c.setTransparency t
    c'.config.toKey = c'.key := by
  obtain ⟨cfg, k⟩ := c
  simp only [ConfigWithKey.setTransparency] at h ⊢
  subst h
  simp only [Config.toKey, UInt64.shiftRight_or, UInt64.shiftLeft_or,
             show cfg.transparency.toUInt64 >>> (3:UInt64) = 0 from by cases cfg.transparency <;> rfl,
             UInt64.zero_or]
  repeat rw [shiftLeft_shiftRight_shiftLeft_of_three_le _ _ (by decide) (by decide)]
  -- Without generalizing these away, the proof is too slow.
  -- We could use `bv_decide` at the cost of heavier imports.
  generalize (_ : UInt64) <<< _ = a,
    (_ : UInt64) <<< _ = a, (_ : UInt64) <<< _ = a,
    (_ : UInt64) <<< _ = a, (_ : UInt64) <<< _ = a,
    (_ : UInt64) <<< _ = a, (_ : UInt64) <<< _ = a,
    (_ : UInt64) <<< _ = a, (_ : UInt64) <<< _ = a,
    (_ : UInt64) <<< _ = a, (_ : UInt64) <<< _ = a,
    (_ : UInt64) <<< _ = a, (_ : UInt64) <<< _ = a,
    (_ : UInt64) <<< _ = a, (_ : UInt64) <<< _ = a,
    (_ : UInt64) <<< _ = a, (_ : UInt64) <<< _ = a,
    (_ : UInt64) <<< _ = a, (_ : UInt64) <<< _ = a
  simp only [UInt64.or_assoc, UInt64.or_comm]
