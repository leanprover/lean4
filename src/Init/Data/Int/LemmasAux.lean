/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Int.Order
import Init.Omega


/-!
# Further lemmas about `Int` relying on `omega` automation.
-/

namespace Int

@[simp] theorem toNat_sub' (a : Int) (b : Nat) : (a - b).toNat = a.toNat - b := by
  symm
  simp only [Int.toNat]
  split <;> rename_i x a
  · simp only [Int.ofNat_eq_coe]
    split <;> rename_i y b h
    · simp at h
      omega
    · simp [Int.negSucc_eq] at h
      omega
  · simp only [Nat.zero_sub]
    split <;> rename_i y b h
    · simp [Int.negSucc_eq] at h
      omega
    · rfl

@[simp] theorem toNat_sub_max_self (a : Int) : (a - max a 0).toNat = 0 := by
  simp [toNat]
  split <;> simp_all <;> omega

@[simp] theorem toNat_sub_self_max (a : Int) : (a - max 0 a).toNat = 0 := by
  simp [toNat]
  split <;> simp_all <;> omega

end Int
