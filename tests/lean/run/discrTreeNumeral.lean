/-!
  # Simp lemmas can match numerals and constant offsets
-/

def MyProp (_ : Nat) : Prop := True

variable (n : Nat)

theorem myProp_zero : MyProp 0 = True := rfl
theorem myProp_add_one : MyProp (n + 1) = True := rfl
theorem myProp_ofNat : MyProp (OfNat.ofNat n) = True := rfl
theorem myProp_ofNat_add_one : MyProp (OfNat.ofNat (n + 1)) = True := rfl

/-- Lemmas about a specific numeral match that numeral. -/
example : MyProp 0 := by
  dsimp only [myProp_zero]

/-- Lemmas about all numerals match a specific numeral.

  (Regression test for https://github.com/leanprover/lean4/issues/2867)-/
example : MyProp 0 := by
  dsimp only [myProp_ofNat]

/-- Lemmas about any natural number plus a constant offset match their left-hand side. -/
example : MyProp (n + 1) := by
  dsimp only [myProp_add_one]

/-- Lemmas about any natural number plus a constant offset match a larger offset. -/
example : MyProp (n + 2) := by
  dsimp only [myProp_add_one]

/-- Lemmas about any natural number plus a constant offset match the constant offset. -/
example : MyProp 1 := by
  dsimp only [myProp_add_one]

/-- Lemmas about any natural number plus a constant offset match constants exceeding the offset. -/
example : MyProp 2 := by
  dsimp only [myProp_add_one]

/-- Lemmas about numerals that express a lower-bound
  through a constant offset match their left-hand side.-/
example : MyProp (OfNat.ofNat (n + 1)) := by
  dsimp only [myProp_ofNat_add_one]

/-- Lemmas about numerals that express a lower-bound
  through a constant offset match a larger offset.-/
example : MyProp (OfNat.ofNat (n + 2)) := by
  dsimp only [myProp_ofNat_add_one]

/-- Lemmas about numerals that express a lower-bound
  through a constant offset match the constant offset.-/
example : MyProp 1 := by
  dsimp only [myProp_ofNat_add_one]

/-- Lemmas about numerals that express a lower-bound
  through a constant offset match numerals exceeding the constant offset.-/
example : MyProp 2 := by
  dsimp only [myProp_ofNat_add_one]

/-- Lemmas about `0` match `Nat.zero` since `Nat.zero = 0` is in the default simp set.-/
example : MyProp Nat.zero := by
  dsimp [myProp_zero]

/-- Lemmas about `0` match `nat_lit 0` since `nat_lit 0 = 0` is in the default simp set.-/
example : MyProp (nat_lit 0) := by
  dsimp [myProp_zero]

/-- Lemmas about any natural number plus a constant offset match their LHS in terms of `Nat.succ`
  since `Nat.succ n = n + 1` is in the default simp set. -/
example : MyProp (Nat.succ n) := by
  dsimp [myProp_add_one]

/-- If a general lemma about numerals is specialized to a particular one, it still applies.

  This is a tricky case because it results in nested `OfNat.ofNat`.
  For example, `(myProp_ofNat 0 : MyProp (OfNat.ofNat (OfNat.ofNat (nat_lit 0)))`.

  This currently works because we're passing an expression instead of a declaration name,
  so `simp` considers it a local hypothesis and bypasses precise discrimination tree matching.
  -/
example : MyProp 0 := by
  dsimp only [myProp_ofNat 0]

/-- If a general lemma about natural numbers plus a constant offset is specialized
  to a constant base, it still applies.

  This is a tricky case because it results in a non-simp-normal lemma statement.
  For example, `(myProp_add_one 0 : MyProp (0 + 1))` can be simplified to `MyProp 1`.-/
example : MyProp 1 := by
  dsimp only [myProp_add_one 0]

/-- If a general lemma about numerals that expresses a lower-bound
  through a constant offset is specialized to a constant base, it still applies.-/
example : MyProp 1 := by
  dsimp only [myProp_ofNat_add_one 0]

class MyClass (n : Nat) : Prop where

instance myClass_succ [MyClass n] : MyClass (n.succ) := ⟨⟩

section BaseZero

local instance myClass_nat_zero : MyClass (Nat.zero) := ⟨⟩

/-- A base instance for `P Nat.zero` and a step instance for `P n → P (n.succ)` can combine to reach any
  sequence of `Nat.zero...succ.succ`.

  Because the kernel has special handling for unifying `Nat.succ`,
  this requires that they can also combine to reach any numeral.

  For example, to reach `P (Nat.zero.succ.succ)`,
  the first recursive step contains the unification problem `P (Nat.zero.succ.succ) =?= P (?n.succ)`,
  which the kernel solves by setting `?n := 1`, *not* `?n := Nat.zero.succ`.
  Thereafter, we need to be able to reach the numeral `1`. -/
example : MyClass (Nat.zero.succ.succ) :=
  inferInstance

#check show Nat.zero.succ.succ = Nat.succ _ from rfl -- Nat.zero.succ.succ = Nat.succ 1

example : MyClass 1 :=
  inferInstance

example : MyClass 0 :=
  inferInstance

end BaseZero

section BaseOne

local instance myClass_succ_nat_zero : MyClass (Nat.zero.succ) := ⟨⟩

/-- A base instance for `P Nat.zero.succ`
  and a step instance for `P n → P (n.succ)` can combine
  to reach any sequence of `Nat.zero.succ...succ.succ`.

  Because the kernel has special handling for unifying `Nat.succ`,
  this requires that they can also combine to reach any numeral greater than `0`.-/
example : MyClass (Nat.zero.succ.succ) :=
  inferInstance

example : MyClass 1 :=
  inferInstance

end BaseOne
