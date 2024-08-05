/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.UnitVal
import Std.Time.Bounded
import Std.Time.LessEq
import Lean.Data.Rat
import Std.Time.Date.Unit.Day
import Std.Time.Date.Unit.Month

namespace Std
namespace Time

set_option linter.all true

namespace WeekOfYear

/--
`Ordinal` represents a bounded value for weeks, which ranges between 1 and 53.
-/
def Ordinal := Bounded.LE 1 53
  deriving Repr, BEq, LE, LT

instance [Le 1 n] [Le n 53] : OfNat Ordinal n where
  ofNat := Bounded.LE.mk (Int.ofNat n) (And.intro (Int.ofNat_le.mpr Le.p) (Int.ofNat_le.mpr Le.p))

instance : Inhabited Ordinal where default := 1

/--
`Offset` represents an offset in weeks. It is defined as an `Int`.
-/
def Offset : Type := UnitVal (86400 * 7)
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, LE, LT, ToString

instance : OfNat Offset n := ⟨UnitVal.ofNat n⟩

namespace Ordinal

/--
Creates an `Ordinal` from a natural number, ensuring the value is within bounds.
-/
def ofNat (data : Nat) (h : data ≥ 1 ∧ data ≤ 53 := by decide) : Ordinal :=
  Bounded.LE.ofNat' data h

/--
Creates an `Ordinal` from a `Fin`, ensuring the value is within bounds.
-/
def ofFin (data : Fin 54) : Ordinal :=
  Bounded.LE.ofFin' data (by decide)

/--
Converts an `Ordinal` to an `Offset`.
-/
def toOffset (ordinal : Ordinal) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal

end WeekOfYear
end Time
end Std
