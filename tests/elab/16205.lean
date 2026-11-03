module

/-! Regression test for cases on USize -/

def five : USize := USize.ofNatLT 5 (Nat.lt_of_lt_of_le (by decide) USize.le_size)

def viaMatch (o : Option USize) : Nat :=
  match o with
  | some ⟨b⟩ => b.toNat
  | none => 0

theorem kernel : viaMatch (some five) = 5 := by decide
/--
error: Tactic `native_decide` evaluated that the proposition
  viaMatch (some five) = 2
is false
-/
#guard_msgs in
theorem compiled : viaMatch (some five) = 2 := by native_decide

theorem compiled' : viaMatch (some five) = 5 := by native_decide

/-- info: 5 -/
#guard_msgs in
#eval viaMatch (some five)
