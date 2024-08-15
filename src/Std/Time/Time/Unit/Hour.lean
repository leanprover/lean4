/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Data.Rat
import Std.Time.Internal
import Std.Time.Time.Unit.Minute
import Std.Time.Time.Unit.Second

namespace Std
namespace Time
namespace Hour
open Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for hour, which ranges between 0 and 24. It is bounded to 24
because 24:00:00 is a valid date with leap seconds.
-/
def Ordinal (leap : Bool) := Bounded.LE 0 (.ofNat (if leap then 24 else 23))

instance : Repr (Ordinal l) where
  reprPrec r l := reprPrec r.val l

instance : OfNat (Ordinal leap) n := by
  have inst := inferInstanceAs (OfNat (Bounded.LE 0 (0 + (23 : Nat))) n)
  cases leap
  · exact inst
  · exact ⟨inst.ofNat.expandTop (by decide)⟩

instance : OfNat (Ordinal true) 24 where
  ofNat := Bounded.LE.mk (Int.ofNat 24) (by decide)

/--
`Offset` represents an offset in hour. It is defined as an `Int`.
-/
def Offset : Type := UnitVal 3600
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

namespace Ordinal

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≤ (if leap then 24 else 23)) : Ordinal leap :=
  Bounded.LE.ofNat data h

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds.
-/
@[inline]
def ofFin (data : Fin (if leap then 25 else 24)) : Ordinal leap :=
  match leap with
  | true => Bounded.LE.ofFin data
  | false => Bounded.LE.ofFin data

/--
Converts an `Ordinal` to an `Offset`.
-/
@[inline]
def toOffset (ordinal : Ordinal leap) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal

namespace Offset

/--
Convert the `Hour` offset to a `Second` Offset.
-/
@[inline]
def toSeconds (val : Offset) : Second.Offset :=
  val.mul 3600

/--
Convert the `Hour` offset to a `Minute` Offset.
-/
@[inline]
def toMinutes (val : Offset) : Minute.Offset :=
  val.mul 60

end Offset
end Hour
end Time
end Std
