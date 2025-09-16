/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Internal
public import Std.Time.Time.Unit.Nanosecond

public section

namespace Std
namespace Time
namespace Millisecond
open Std.Internal
open Internal

set_option linter.all true
set_option linter.missingDocs true
set_option doc.verso true

/--
{name}`Ordinal` represents a bounded value for milliseconds, ranging from 0 to 999 milliseconds.
-/
@[expose] def Ordinal := Bounded.LE 0 999
deriving Repr, DecidableEq, LE, LT

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 0 (0 + (999 : Nat))) n)

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
{name}`Offset` represents a duration offset in milliseconds.
-/
@[expose] def Offset : Type := UnitVal (1 / 1000)
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
Creates an {name}`Offset` from a natural number.
-/
@[inline]
def ofNat (data : Nat) : Offset :=
  UnitVal.ofInt data

/--
Creates an {name}`Offset` from an integer.
-/
@[inline]
def ofInt (data : Int) : Offset :=
  UnitVal.ofInt data

end Offset
namespace Ordinal

/--
Creates an {name}`Ordinal` from an integer, ensuring the value is within bounds.
-/
@[inline]
def ofInt (data : Int) (h : 0 ≤ data ∧ data ≤ 999) : Ordinal :=
  Bounded.LE.mk data h

/--
Creates an {name}`Ordinal` from a natural number, ensuring the value is within bounds.
-/
@[inline]
def ofNat (data : Nat) (h : data ≤ 999) : Ordinal :=
  Bounded.LE.ofNat data h

/--
Creates an {name}`Ordinal` from a {name}`Fin`, ensuring the value is within bounds.
-/
@[inline]
def ofFin (data : Fin 1000) : Ordinal :=
  Bounded.LE.ofFin data

/--
Converts an {name}`Ordinal` to an {name}`Offset`.
-/
@[inline]
def toOffset (ordinal : Ordinal) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal
end Millisecond
end Time
end Std
