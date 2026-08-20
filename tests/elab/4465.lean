/-- info: { val := { toBitVec := { toFin := ⟨0, ⋯⟩ } }, valid := ⋯ } -/
#guard_msgs in
#reduce Char.ofNat (nat_lit 0)

/--
info: { val := { toBitVec := { toFin := ⟨0, Char.ofNatAux._private_1 0 (Decidable.reflects_decide (Nat.isValidChar 0))⟩ } },
  valid := Decidable.reflects_decide (Nat.isValidChar 0) }
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
