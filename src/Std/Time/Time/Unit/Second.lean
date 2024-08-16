/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Data.Rat
import Std.Time.Time.Unit.Nanosecond

namespace Std
namespace Time
namespace Second
open Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for second, which ranges between 0 and 59 or 60. This accounts
for potential leap second.
-/
def Ordinal (leap : Bool) := Bounded.LE 0 (.ofNat (if leap then 60 else 59))

instance : Repr (Ordinal l) where
  reprPrec r l := reprPrec r.val l

instance : OfNat (Ordinal leap) n := by
  have inst := inferInstanceAs (OfNat (Bounded.LE 0 (0 + (59 : Nat))) n)
  cases leap
  · exact inst
  · exact ⟨inst.ofNat.expandTop (by decide)⟩

instance : OfNat (Ordinal true) 60 where
  ofNat := Bounded.LE.mk (Int.ofNat 60) (by decide)

/--
`Offset` represents an offset in seconds. It is defined as an `Int`.
-/
def Offset : Type := UnitVal 1
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, LE, LT, ToString

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

namespace Ordinal

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≤ (if leap then 60 else 59)) : Ordinal leap :=
  Bounded.LE.ofNat data h

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds.
-/
@[inline]
def ofFin (data : Fin (if leap then 61 else 60)) : Ordinal leap :=
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
end Second
end Time
end Std
