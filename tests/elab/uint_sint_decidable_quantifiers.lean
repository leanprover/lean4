/-!
Tests the `Decidable` instances for `∀ x, P x` and `∃ x, P x` over `UIntX` and `IntX` from
`Init.Data.UInt.Decidable` and `Init.Data.SInt.Decidable`.
-/

/-! The instances are found by type class inference. -/

/-- info: UInt8.instDecidableForall fun x => x = x -/
#guard_msgs in
#synth Decidable (∀ x : UInt8, x = x)

/-- info: Int64.instDecidableExists fun x => x = 0 -/
#guard_msgs in
#synth Decidable (∃ x : Int64, x = 0)

example : Decidable (∀ x : UInt16, x = x) := inferInstance
example : Decidable (∀ x : UInt32, x = x) := inferInstance
example : Decidable (∀ x : UInt64, x = x) := inferInstance
example : Decidable (∃ x : UInt8, x = 0) := inferInstance
example : Decidable (∃ x : UInt16, x = 0) := inferInstance
example : Decidable (∃ x : UInt32, x = 0) := inferInstance
example : Decidable (∃ x : UInt64, x = 0) := inferInstance
example : Decidable (∀ x : Int8, x = x) := inferInstance
example : Decidable (∀ x : Int16, x = x) := inferInstance
example : Decidable (∀ x : Int32, x = x) := inferInstance
example : Decidable (∀ x : Int64, x = x) := inferInstance
example : Decidable (∃ x : Int8, x = 0) := inferInstance
example : Decidable (∃ x : Int16, x = 0) := inferInstance
example : Decidable (∃ x : Int32, x = 0) := inferInstance

/-! The underlying lemmas reduce to quantifiers over `BitVec`. -/

example {P : UInt8 → Prop} : (∀ x, P x) ↔ ∀ x : BitVec 8, P (UInt8.ofBitVec x) :=
  UInt8.forall_iff_forall_ofBitVec
example {P : UInt16 → Prop} : (∃ x, P x) ↔ ∃ x : BitVec 16, P (UInt16.ofBitVec x) :=
  UInt16.exists_iff_exists_ofBitVec
example {P : UInt32 → Prop} : (∀ x, P x) ↔ ∀ x : BitVec 32, P (UInt32.ofBitVec x) :=
  UInt32.forall_iff_forall_ofBitVec
example {P : UInt64 → Prop} : (∃ x, P x) ↔ ∃ x : BitVec 64, P (UInt64.ofBitVec x) :=
  UInt64.exists_iff_exists_ofBitVec
example {P : Int8 → Prop} : (∃ x, P x) ↔ ∃ x : BitVec 8, P (Int8.ofBitVec x) :=
  Int8.exists_iff_exists_ofBitVec
example {P : Int16 → Prop} : (∀ x, P x) ↔ ∀ x : BitVec 16, P (Int16.ofBitVec x) :=
  Int16.forall_iff_forall_ofBitVec
example {P : Int32 → Prop} : (∃ x, P x) ↔ ∃ x : BitVec 32, P (Int32.ofBitVec x) :=
  Int32.exists_iff_exists_ofBitVec
example {P : Int64 → Prop} : (∀ x, P x) ↔ ∀ x : BitVec 64, P (Int64.ofBitVec x) :=
  Int64.forall_iff_forall_ofBitVec

/-! `decide` enumerates all values of the 8-bit types in the kernel. -/

example : ∀ x : UInt8, x.toNat < 256 := by decide
example : ∀ b : UInt8, b.isUTF8ContinuationByte ↔ 0x80 ≤ b ∧ b < 0xc0 := by decide
example : ∃ x : UInt8, x ≠ 0 ∧ x * x = 0 := by decide
example : ¬ ∃ x : UInt8, x * x = 2 := by decide
example : ∀ x : Int8, -128 ≤ x.toInt ∧ x.toInt < 128 := by decide
example : ∃ x : Int8, x + 1 < x := by decide
example : ∀ x : Int8, -x = x → x = 0 ∨ x = -128 := by decide

/-! For wider types, `decide` succeeds when the search terminates early: values are enumerated
in increasing order of their underlying bit vector. At 64 bits, the elaborator's evaluation of the
`BitVec` instance exceeds `maxRecDepth`, so we check those in the kernel directly. -/

example : ∃ x : UInt16, x * x = 49 := by decide
example : ∃ x : UInt32, x * x = 49 := by decide
example : ∃ x : UInt64, x * x = 49 := by decide +kernel
example : ¬ ∀ x : Int16, x * x ≠ 49 := by decide
example : ¬ ∀ x : Int32, x * x ≠ 49 := by decide
example : ¬ ∀ x : Int64, x * x ≠ 49 := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  ∀ (x : UInt8), x < 255
is false
-/
#guard_msgs in
example : ∀ x : UInt8, x < 255 := by decide

/--
error: Tactic `decide` proved that the proposition
  ∃ x, x * x = 2
is false
-/
#guard_msgs in
example : ∃ x : Int8, x * x = 2 := by decide

/-! The compiled instances enumerate all values of the 16-bit types and handle nested quantifiers,
which are too slow for `decide`. -/

#guard ∀ x : UInt16, x.toNat < 65536
#guard ∀ x : Int16, -32768 ≤ x.toInt ∧ x.toInt < 32768
#guard ∃ x : UInt16, x ≠ 0 ∧ x * x = 0
#guard ¬ ∃ x : Int16, x * x = 2
#guard ∃ x : Int16, x + 1 < x
#guard ∃ x : Int32, x * x = 49
#guard ¬ ∀ x : UInt64, x * x ≠ 49
#guard ∀ x : UInt8, ∃ y : Int8, y.toUInt8 = x
#guard ∀ x : Int8, ∃ y : Int8, x + y = 0
#guard ∃ x : UInt8, ∀ y : UInt8, x * y = y
#guard ¬ ∃ x : Int8, ∀ y : Int8, y < x
