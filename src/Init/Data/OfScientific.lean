/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Float.Float32
import Init.Data.Nat.Log2
import Init.Meta
import Init.Data.Array.Lemmas

public section

/-- For decimal and scientific numbers (e.g., `1.23`, `3.12e10`).
   Examples:
   - `1.23` is syntax for `OfScientific.ofScientific (nat_lit 123) true (nat_lit 2)`
   - `121e100` is syntax for `OfScientific.ofScientific (nat_lit 121) false (nat_lit 100)`

   Note the use of `nat_lit`; there is no wrapping `OfNat.ofNat` in the resulting term.
-/
class OfScientific (α : Type u) where
  /--
  Produces a value from the given mantissa, exponent sign, and decimal exponent. For the exponent
  sign, `true` indicates a negative exponent.

   Examples:
   - `1.23` is syntax for `OfScientific.ofScientific (nat_lit 123) true (nat_lit 2)`
   - `121e100` is syntax for `OfScientific.ofScientific (nat_lit 121) false (nat_lit 100)`

   Note the use of `nat_lit`; there is no wrapping `OfNat.ofNat` in the resulting term.
  -/
  ofScientific (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) : α

/--
Precomputed values of `10 ^ e` for `0 ≤ e ≤ 22`. In this range, the values can be represented
exactly.
-/
@[expose] def Float.exactlyRepresentablePowersOfTen : Array Float :=
 #[Float.ofBits 0x3FF0000000000000, Float.ofBits 0x4024000000000000,
   Float.ofBits 0x4059000000000000, Float.ofBits 0x408F400000000000,
   Float.ofBits 0x40C3880000000000, Float.ofBits 0x40F86A0000000000,
   Float.ofBits 0x412E848000000000, Float.ofBits 0x416312D000000000,
   Float.ofBits 0x4197D78400000000, Float.ofBits 0x41CDCD6500000000,
   Float.ofBits 0x4202A05F20000000, Float.ofBits 0x42374876E8000000,
   Float.ofBits 0x426D1A94A2000000, Float.ofBits 0x42A2309CE5400000,
   Float.ofBits 0x42D6BCC41E900000, Float.ofBits 0x430C6BF526340000,
   Float.ofBits 0x4341C37937E08000, Float.ofBits 0x4376345785D8A000,
   Float.ofBits 0x43ABC16D674EC800, Float.ofBits 0x43E158E460913D00,
   Float.ofBits 0x4415AF1D78B58C40, Float.ofBits 0x444B1AE4D6E2EF50,
   Float.ofBits 0x4480F0CF064DD592]

@[expose] protected def Float.ofScientific (m : Nat) (s : Bool) (e : Nat) : Float :=
  if h : m < 2 ^ 53 ∧ e ≤ 22 then
    -- Fast case: both `m` and `10 ^ e` are representable as floats.
    let powerOfTen : Float :=
      exactlyRepresentablePowersOfTen[e]'(by simp [exactlyRepresentablePowersOfTen]; omega)
    if s then
      m.toUInt64.toFloat / powerOfTen
    else
      m.toUInt64.toFloat * powerOfTen
  else
    -- Slow case. Implementing this efficiently is difficult. The comparatively simple algorithm at
    -- https://www.exploringbinary.com/correct-decimal-to-floating-point-using-big-integers/
    -- is difficult to get right in the case of subnormals and isn't faster than just going through
    -- the model. So, we go through the model.
    let e := if s then Int.negOfNat e else Int.ofNat e
    Float.ofModel (Float.Model.ofScientific m e)

/--
  The `OfScientific Float` must have priority higher than `mid` since
  the default instance `Neg Int` has `mid` priority.
  ```
  #check -42.0 -- must be Float
  ```
-/
@[default_instance mid+1]
instance : OfScientific Float where
  ofScientific := Float.ofScientific

/--
Converts a natural number into the closest-possible 64-bit floating-point number, or an infinite
floating-point value if the range of `Float` is exceeded.
-/
@[export lean_float_of_nat]
def Float.ofNat (n : Nat) : Float :=
  OfScientific.ofScientific n false 0

/--
Converts an integer into the closest-possible 64-bit floating-point number, or positive or negative
infinite floating-point value if the range of `Float` is exceeded.
-/
def Float.ofInt : Int → Float
  | Int.ofNat n => Float.ofNat n
  | Int.negSucc n => Float.neg (Float.ofNat (Nat.succ n))

instance : OfNat Float n   := ⟨Float.ofNat n⟩

@[inherit_doc Float.ofNat] abbrev Nat.toFloat (n : Nat) : Float :=
  Float.ofNat n

/--
Precomputed values of `10 ^ e` for `0 ≤ e ≤ 10 `. In this range, the values can be represented
exactly.
-/
@[expose] def Float32.exactlyRepresentablePowersOfTen : Array Float32 :=
 #[Float32.ofBits 0x3F800000, Float32.ofBits 0x41200000, Float32.ofBits 0x42C80000,
   Float32.ofBits 0x447A0000, Float32.ofBits 0x461C4000, Float32.ofBits 0x47C35000,
   Float32.ofBits 0x49742400, Float32.ofBits 0x4B189680, Float32.ofBits 0x4CBEBC20,
   Float32.ofBits 0x4E6E6B28, Float32.ofBits 0x501502F9]

@[expose] protected def Float32.ofScientific (m :Nat) (s : Bool) (e : Nat) : Float32 :=
  -- See comments on `Float.ofScientific`.
  if h : m < 2 ^ 23 ∧ e ≤ 10 then
    let powerOfTen : Float32 :=
      exactlyRepresentablePowersOfTen[e]'(by simp [exactlyRepresentablePowersOfTen]; omega)
    if s then
      m.toUInt64.toFloat32 / powerOfTen
    else
      m.toUInt64.toFloat32 * powerOfTen
  else
    let e := if s then Int.negOfNat e else Int.ofNat e
    Float32.ofModel (Float32.Model.ofScientific m e)

instance : OfScientific Float32 where
  ofScientific := Float32.ofScientific

/--
Converts a natural number into the closest-possible 32-bit floating-point number, or an infinite
floating-point value if the range of `Float32` is exceeded.
-/
@[export lean_float32_of_nat]
def Float32.ofNat (n : Nat) : Float32 :=
  OfScientific.ofScientific n false 0

/--
Converts an integer into the closest-possible 32-bit floating-point number, or positive or negative
infinite floating-point value if the range of `Float32` is exceeded.
-/
def Float32.ofInt : Int → Float32
  | Int.ofNat n => Float32.ofNat n
  | Int.negSucc n => Float32.neg (Float32.ofNat (Nat.succ n))

instance : OfNat Float32 n   := ⟨Float32.ofNat n⟩

@[inherit_doc Float32.ofNat] abbrev Nat.toFloat32 (n : Nat) : Float32 :=
  Float32.ofNat n
