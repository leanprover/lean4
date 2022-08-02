/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta
import Init.Data.Float
import Init.Data.Nat

/-- For decimal and scientific numbers (e.g., `1.23`, `3.12e10`).
   Examples:
   - `OfScientific.ofScientific 123 true 2`    represents `1.23`
   - `OfScientific.ofScientific 121 false 100` represents `121e100`
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
@[defaultInstance mid+1]
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
