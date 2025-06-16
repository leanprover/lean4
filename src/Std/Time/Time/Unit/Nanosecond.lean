/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Rat
import Std.Time.Internal

namespace Std
namespace Time
namespace Nanosecond
open Std.Internal
open Internal

set_option linter.all true

/--
`Ordinal` represents a nanosecond value that is bounded between 0 and 999,999,999 nanoseconds.
-/
def Ordinal := Bounded.LE 0 999999999
deriving Repr, DecidableEq, LE, LT

instance : OfNat Ordinal n where
  ofNat := Bounded.LE.ofFin (Fin.ofNat' _ n)

instance : Inhabited Ordinal where
  default := 0

instance {x y : Ordinal} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Ordinal} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

instance : Ord Ordinal := inferInstanceAs <| Ord (Bounded.LE 0 _)

instance : TransOrd Ordinal := inferInstanceAs <| TransOrd (Bounded.LE 0 _)

instance : LawfulEqOrd Ordinal := inferInstanceAs <| LawfulEqOrd (Bounded.LE 0 _)

/--
`Offset` represents a time offset in nanoseconds.
-/
def Offset : Type := UnitVal (1 / 1000000000)
deriving Repr, DecidableEq, Inhabited, Add, Sub, Neg, LE, LT, ToString

instance {x y : Offset} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Offset} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

instance : OfNat Offset n :=
  ⟨UnitVal.ofNat n⟩

instance : Ord Offset := inferInstanceAs <| Ord (UnitVal _)

instance : TransOrd Offset := inferInstanceAs <| TransOrd (UnitVal _)

instance : LawfulEqOrd Offset := inferInstanceAs <| LawfulEqOrd (UnitVal _)

namespace Offset

/--
Creates an `Offset` from a natural number.
-/
@[inline]
def ofNat (data : Nat) : Offset :=
  UnitVal.ofInt data

/--
Creates an `Offset` from an integer.
-/
@[inline]
def ofInt (data : Int) : Offset :=
  UnitVal.ofInt data

end Offset

/--
`Span` represents a bounded value for nanoseconds, ranging between -999999999 and 999999999.
This can be used for operations that involve differences or adjustments within this range.
-/
def Span := Bounded.LE (-999999999) 999999999
deriving Repr, DecidableEq, LE, LT

instance : Inhabited Span where default := Bounded.LE.mk 0 (by decide)

instance {x y : Span} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Span} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

instance : Ord Span := inferInstanceAs <| Ord (Bounded.LE _ _)

instance : TransOrd Span := inferInstanceAs <| TransOrd (Bounded.LE _ _)

instance : LawfulEqOrd Span := inferInstanceAs <| LawfulEqOrd (Bounded.LE _ _)

namespace Span

/--
Creates a new `Offset` out of a `Span`.
-/
def toOffset (span : Span) : Offset :=
  UnitVal.ofInt span.val

end Span

namespace Ordinal

/--
`Ordinal` represents a bounded value for nanoseconds in a day, which ranges between 0 and 86400000000000.
-/
def OfDay := Bounded.LE 0 86400000000000
deriving Repr, DecidableEq, LE, LT

instance : Inhabited OfDay where default := Bounded.LE.mk 0 (by decide)

instance {x y : OfDay} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : OfDay} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

instance : Ord OfDay := inferInstanceAs <| Ord (Bounded.LE _ _)

instance : TransOrd OfDay := inferInstanceAs <| TransOrd (Bounded.LE _ _)

instance : LawfulEqOrd OfDay := inferInstanceAs <| LawfulEqOrd (Bounded.LE _ _)

/--
Creates an `Ordinal` from an integer, ensuring the value is within bounds.
-/
@[inline]
def ofInt (data : Int) (h : 0 ≤ data ∧ data ≤ 999999999) : Ordinal :=
  Bounded.LE.mk data h

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≤ 999999999) : Ordinal :=
  Bounded.LE.ofNat data h

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds.
-/
@[inline]
def ofFin (data : Fin 1000000000) : Ordinal :=
  Bounded.LE.ofFin data

/--
Converts an `Ordinal` to an `Offset`.
-/
@[inline]
def toOffset (ordinal : Ordinal) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal
end Nanosecond
end Time
end Std
