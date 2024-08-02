/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.UnitVal
import Lean.Time.Date.Basic

namespace Lean
namespace Date

/--
`Scalar` represents a date offset, using the number of day as the underlying unit.
-/
structure Scalar where
  day : Day.Offset
  deriving Repr, BEq, Inhabited

instance : Add Scalar where add x y := ⟨x.day + y.day⟩
instance : Sub Scalar where sub x y := ⟨x.day - y.day⟩
instance : Mul Scalar where mul x y := ⟨x.day * y.day⟩
instance : Div Scalar where div x y := ⟨x.day / y.day⟩
instance : Neg Scalar where neg x := ⟨-x.day⟩

namespace Scalar

/--
Creates a `Scalar` from a given number of day.
-/
def ofDays (day : Int) : Scalar :=
  ⟨UnitVal.ofInt day⟩

/--
Retrieves the number of day from a `Scalar`.
-/
def toDays (scalar : Scalar) : Int :=
  scalar.day.val

/--
Adds a specified number of day to the `Scalar`, returning a new `Scalar`.
-/
def addDays (scalar : Scalar) (day : Day.Offset) : Scalar :=
  ⟨scalar.day + day⟩

/--
Subtracts a specified number of day from the `Scalar`, returning a new `Scalar`.
-/
def subDays (scalar : Scalar) (day : Day.Offset) : Scalar :=
  ⟨scalar.day - day⟩

/--
Converts a `Scalar` to a `Day.Offset`.
-/
def toOffset (scalar : Scalar) : Day.Offset :=
  scalar.day

/--
Creates a `Scalar` from a `Day.Offset`.
-/
def ofOffset (offset : Day.Offset) : Scalar :=
  ⟨offset⟩

end Scalar
end Date
