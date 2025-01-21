/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Rat
import Std.Time.Time.Unit.Nanosecond

namespace Std
namespace Time
namespace Second
open Std.Internal
open Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for second, which ranges between 0 and 59 or 60. This accounts
for potential leap second.
-/
def Ordinal (leap : Bool) := Bounded.LE 0 (.ofNat (if leap then 60 else 59))

instance : BEq (Ordinal leap) where
  beq x y := BEq.beq x.val y.val

instance : LE (Ordinal leap) where
  le x y := LE.le x.val y.val

instance : LT (Ordinal leap) where
  lt x y := LT.lt x.val y.val

instance : Repr (Ordinal l) where
  reprPrec r := reprPrec r.val

instance : OfNat (Ordinal leap) n := by
  have inst := inferInstanceAs (OfNat (Bounded.LE 0 (0 + (59 : Nat))) n)
  cases leap
  · exact inst
  · exact ⟨inst.ofNat.expandTop (by decide)⟩

instance {x y : Ordinal l} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Ordinal l} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

/--
`Offset` represents an offset in seconds. It is defined as an `Int`.
-/
def Offset : Type := UnitVal 1
  deriving Repr, BEq, Inhabited, Add, Sub, Neg, LE, LT, ToString

instance : OfNat Offset n :=
  ⟨UnitVal.ofNat n⟩

namespace Offset

/--
Creates an `Second.Offset` from a natural number.
-/
@[inline]
def ofNat (data : Nat) : Second.Offset :=
  UnitVal.ofInt data

/--
Creates an `Second.Offset` from an integer.
-/
@[inline]
def ofInt (data : Int) : Second.Offset :=
  UnitVal.ofInt data

end Offset

namespace Ordinal

/--
Creates an `Ordinal` from an integer, ensuring the value is within bounds.
-/
@[inline]
def ofInt (data : Int) (h : 0 ≤ data ∧ data ≤ Int.ofNat (if leap then 60 else 59)) : Ordinal leap :=
  Bounded.LE.mk data h

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
Converts an `Ordinal` to an `Second.Offset`.
-/
@[inline]
def toOffset (ordinal : Ordinal leap) : Second.Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal
end Second
end Time
end Std
