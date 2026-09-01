structure PreInt where
  minuend : Nat
  subtrahend : Nat

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by grind
    symm := by grind
    trans := by grind
  }

abbrev MyInt := Quotient PreInt.instSetoid

abbrev MyInt.formalDiff (a b : Nat) : MyInt := Quotient.mk PreInt.instSetoid ⟨ a, b ⟩

theorem MyInt.eq (a b c d : Nat) : formalDiff a b = formalDiff c d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

instance MyInt.instOfNat {n : Nat} : OfNat MyInt n where
  ofNat := formalDiff n 0

instance MyInt.instNatCast : NatCast MyInt where
  natCast n := formalDiff n 0

theorem MyInt.natCast_eq (n : Nat) : (n : MyInt) = formalDiff n 0 := rfl

theorem MyInt.natCast_inj (n m : Nat) :
  (n : MyInt) = (m : MyInt) ↔ n = m := by
  rw [natCast_eq, natCast_eq, eq]; simp

example (n m : Nat) : (n : MyInt) = (m : MyInt) ↔ n = m := by
  grind [MyInt.natCast_eq, MyInt.eq]

@[grind]
theorem MyInt.eq_0_of_cast_eq_0 (n : Nat) (h : (n : MyInt) = 0) : n = 0 := by
  rw [show (0 : MyInt) = ((0 : Nat) : MyInt) by rfl] at h
  rwa [natCast_inj] at h

theorem MyInt.pos_iff_gt_0 {a : MyInt} : (∃ (n:Nat), n > 0 ∧ a = n) → a ≠ 0 := by
  intro ⟨ w, hw ⟩ h
  grind

example {a : MyInt} : (∃ (n:Nat), n > 0 ∧ a = n) → a ≠ 0 := by
  grind
