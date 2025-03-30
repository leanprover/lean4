/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Classes.Ord
import Std.Internal.Rat

namespace Std
namespace Time
namespace Internal
open Std.Internal
open Lean

set_option linter.all true

/--
A structure representing a unit of a given ratio type `α`.
-/
@[ext]
structure UnitVal (α : Rat) where
  /--
  Creates a `UnitVal` from an `Int`.
  -/
  ofInt ::

  /--
  Value inside the UnitVal Value.
  -/
  val : Int
deriving Inhabited, DecidableEq

instance : LE (UnitVal x) where
  le x y := x.val ≤ y.val

instance : Ord (UnitVal x) where
  compare x y := compare x.val y.val

theorem UnitVal.compare_def {x} {a b : UnitVal x} :
    compare a b = compare a.1 b.1 := by rfl

instance : OrientedOrd (UnitVal x) where
  eq_swap := OrientedOrd.eq_swap (α := Int)

instance : TransOrd (UnitVal x) where
  isLE_trans := TransOrd.isLE_trans (α := Int)

instance : LawfulEqOrd (UnitVal x) where
  eq_of_compare := UnitVal.ext ∘ LawfulEqOrd.eq_of_compare (α := Int)

instance {x y : UnitVal z}: Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

namespace UnitVal

/--
Creates a `UnitVal` from a `Nat`.
-/
@[inline]
def ofNat (value : Nat) : UnitVal α :=
  ⟨value⟩

/--
Converts a `UnitVal` to an `Int`.
-/
@[inline]
def toInt (unit : UnitVal α) : Int :=
  unit.val

/--
Multiplies the `UnitVal` by an `Int`, resulting in a new `UnitVal` with an adjusted ratio.
-/
@[inline]
def mul (unit : UnitVal a) (factor : Int) : UnitVal (a / factor) :=
  ⟨unit.val * factor⟩

/--
Divides the `UnitVal` by an `Int`, resulting in a new `UnitVal` with an adjusted ratio. Using the
E-rounding convention (euclidean division)
-/
@[inline]
def ediv (unit : UnitVal a) (divisor : Int) : UnitVal (a * divisor) :=
  ⟨unit.val.ediv divisor⟩

/--
Divides the `UnitVal` by an `Int`, resulting in a new `UnitVal` with an adjusted ratio. Using the
"T-rounding" (Truncation-rounding) convention
-/
@[inline]
def tdiv (unit : UnitVal a) (divisor : Int) : UnitVal (a * divisor) :=
  ⟨unit.val.tdiv divisor⟩

/--
Divides the `UnitVal` by an `Int`, resulting in a new `UnitVal` with an adjusted ratio.
-/
@[inline]
def div (unit : UnitVal a) (divisor : Int) : UnitVal (a * divisor) :=
  ⟨unit.val.tdiv divisor⟩

/--
Adds two `UnitVal` values of the same ratio.
-/
@[inline]
def add (u1 : UnitVal α) (u2 : UnitVal α) : UnitVal α :=
  ⟨u1.val + u2.val⟩

/--
Subtracts one `UnitVal` value from another of the same ratio.
-/
@[inline]
def sub (u1 : UnitVal α) (u2 : UnitVal α) : UnitVal α :=
  ⟨u1.val - u2.val⟩

/--
Returns the absolute value of a `UnitVal`.
-/
@[inline]
def abs (u : UnitVal α) : UnitVal α :=
  ⟨u.val.natAbs⟩

/--
Converts an `Offset` to another unit type.
-/
@[inline]
def convert (val : UnitVal a) : UnitVal b :=
  let ratio := a.div b
  ofInt <| val.toInt * ratio.num / ratio.den

instance : OfNat (UnitVal α) n where ofNat := ⟨Int.ofNat n⟩

instance : Repr (UnitVal α) where reprPrec x p := reprPrec x.val p

instance : LE (UnitVal α) where le x y := x.val ≤ y.val

instance : LT (UnitVal α) where lt x y := x.val < y.val

instance : Add (UnitVal α) where add := UnitVal.add

instance : Sub (UnitVal α) where sub := UnitVal.sub

instance : Neg (UnitVal α) where neg x := ⟨-x.val⟩

instance : ToString (UnitVal n) where toString n := toString n.val


end UnitVal
end Internal
end Time
end Std
