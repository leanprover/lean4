/-- info: { val := { toBitVec := { toFin := ⟨0, ⋯⟩ } }, valid := ⋯ } -/
#guard_msgs in
#reduce Char.ofNat (nat_lit 0)

/--
info: { val := { toBitVec := { toFin := ⟨0, isValidChar_UInt32✝ (Or.inl (Nat.le_of_ble_eq_true rfl))⟩ } },
  valid := Or.inl (Nat.le_of_ble_eq_true rfl) }
-/
#guard_msgs in
set_option pp.proofs true in
#reduce Char.ofNat (nat_lit 0)

/-- info: 2 = 1 + 1 -/
#guard_msgs in
#reduce 2 = 1 + 1

/-- info: 2 = 2 -/
#guard_msgs in
#reduce (types := true) 2 = 1 + 1

/-- info: Eq.refl (2 + 2) -/
#guard_msgs in
set_option pp.proofs true in
#reduce Eq.refl (2+2)

/-- info: Eq.refl 4 -/
#guard_msgs in
set_option pp.proofs true in
#reduce (proofs := true) Eq.refl (2+2)
