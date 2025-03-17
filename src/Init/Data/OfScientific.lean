/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta
import Init.Data.Float
import Init.Data.Float32
import Init.Data.Nat.Log2

/-- For decimal and scientific numbers (e.g., `1.23`, `3.12e10`).
   Examples:
   - `1.23` is syntax for `OfScientific.ofScientific (nat_lit 123) true (nat_lit 2)`
   - `121e100` is syntax for `OfScientific.ofScientific (nat_lit 121) false (nat_lit 100)`

   Note the use of `nat_lit`; there is no wrapping `OfNat.ofNat` in the resulting term.
-/
class OfScientific (α : Type u) where
  ofScientific (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) : α

/-- Computes `m * 2^e`. -/
def Float.ofBinaryScientific (m : Nat) (e : Int) : Float :=
  let s := m.log2 - 63
  let m := (m >>> s).toUInt64
  let e := e + s
  m.toFloat.scaleB e

protected opaque Float.ofScientific (m : Nat) (s : Bool) (e : Nat) : Float :=
  if s then
    let s := 64 - m.log2 -- ensure we have 64 bits of mantissa left after division
    let m := (m <<< (3 * e + s)) / 5^e
    Float.ofBinaryScientific m (-4 * e - s)
  else
    Float.ofBinaryScientific (m * 5^e) e

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

@[export lean_float_of_nat]
def Float.ofNat (n : Nat) : Float :=
  OfScientific.ofScientific n false 0

def Float.ofInt : Int → Float
  | Int.ofNat n => Float.ofNat n
  | Int.negSucc n => Float.neg (Float.ofNat (Nat.succ n))

instance : OfNat Float n   := ⟨Float.ofNat n⟩

abbrev Nat.toFloat (n : Nat) : Float :=
  Float.ofNat n

/-- Computes `m * 2^e`. -/
def Float32.ofBinaryScientific (m : Nat) (e : Int) : Float32 :=
  let s := m.log2 - 63
  let m := (m >>> s).toUInt64
  let e := e + s
  m.toFloat32.scaleB e

protected opaque Float32.ofScientific (m : Nat) (s : Bool) (e : Nat) : Float32 :=
  if s then
    let s := 64 - m.log2 -- ensure we have 64 bits of mantissa left after division
    let m := (m <<< (3 * e + s)) / 5^e
    Float32.ofBinaryScientific m (-4 * e - s)
  else
    Float32.ofBinaryScientific (m * 5^e) e

instance : OfScientific Float32 where
  ofScientific := Float32.ofScientific

@[export lean_float32_of_nat]
def Float32.ofNat (n : Nat) : Float32 :=
  OfScientific.ofScientific n false 0

def Float32.ofInt : Int → Float32
  | Int.ofNat n => Float32.ofNat n
  | Int.negSucc n => Float32.neg (Float32.ofNat (Nat.succ n))

instance : OfNat Float32 n   := ⟨Float32.ofNat n⟩

abbrev Nat.toFloat32 (n : Nat) : Float32 :=
  Float32.ofNat n
