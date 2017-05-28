/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/

def pnat := {n : ℕ // n > 0}
notation `ℕ+` := pnat

instance coe_pnat_nat : has_coe ℕ+ ℕ := ⟨subtype.val⟩

meta def exact_dec_trivial : tactic unit := `[exact dec_trivial]

namespace nat

  def to_pnat (n : ℕ) (h : n > 0 . exact_dec_trivial) : ℕ+ := ⟨n, h⟩

  def succ_pnat (n : ℕ) : ℕ+ := ⟨succ n, succ_pos n⟩

  def to_pnat' (n : ℕ) : ℕ+ := succ_pnat (pred n)
end nat

instance coe_nat_pnat : has_coe ℕ ℕ+ := ⟨nat.to_pnat'⟩

namespace pnat
  open nat

  instance : has_one ℕ+ := ⟨succ_pnat 0⟩

  protected def add : ℕ+ → ℕ+ → ℕ+
  | ⟨m, m0⟩ ⟨n, n0⟩ := ⟨m + n, add_pos m0 n0⟩

  instance : has_add ℕ+ := ⟨pnat.add⟩

  protected def mul : ℕ+ → ℕ+ → ℕ+
  | ⟨m, m0⟩ ⟨n, n0⟩ := ⟨m * n, mul_pos m0 n0⟩

  instance : has_mul ℕ+ := ⟨pnat.mul⟩

  @[simp] theorem to_pnat'_val {n : ℕ} : n > 0 → n.to_pnat'.val = n := succ_pred_eq_of_pos
  @[simp] theorem nat_coe_val  {n : ℕ} : n > 0 → (n : ℕ+).val = n := succ_pred_eq_of_pos
  @[simp] theorem to_pnat'_coe {n : ℕ} : n > 0 → (n.to_pnat' : ℕ) = n := succ_pred_eq_of_pos

end pnat
