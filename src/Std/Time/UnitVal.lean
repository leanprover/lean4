/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init
import Lean.Data.Rat
import Std.Time.Sign

namespace Std
namespace Time
open Lean

set_option linter.all true

/--
A structure representing a unit of a given ratio type `α`.
-/
structure UnitVal (α : Rat) where
  private mk ::
  /--
  Value inside the UnitVal Value
  -/
  val : Int
  deriving Inhabited, BEq

namespace UnitVal

/--
Creates a `UnitVal` from an `Int`.
-/
@[inline]
def ofInt (value : Int) : UnitVal α :=
  ⟨value⟩

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
Divides the `UnitVal` by an `Int`, resulting in a new `UnitVal` with an adjusted ratio.
-/
@[inline]
def div (unit : UnitVal a) (divisor : Int) : UnitVal (a * divisor) :=
  ⟨unit.val / divisor⟩

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
Apply the `Sign` to a value.
-/
@[inline]
def apply (u1 : UnitVal α) (sign : Sign) : UnitVal α :=
  ⟨u1.val * sign.val⟩



/--
Converts an `Offset` to another unit type.
-/
def convert (val : UnitVal a) : UnitVal b :=
  let ratio := a.div b
  ofInt <| val.toInt * ratio.num / ratio.den

instance : OfNat (UnitVal α) n where ofNat := ⟨Int.ofNat n⟩
instance : Repr (UnitVal α) where reprPrec x p := reprPrec x.val p
instance : LE (UnitVal α) where le x y := x.val ≤ y.val
instance : LT (UnitVal α) where lt x y := x.val < y.val
instance : Add (UnitVal α) where add x y := ⟨x.val + y.val⟩
instance : Sub (UnitVal α) where sub x y := ⟨x.val - y.val⟩
instance : Mul (UnitVal α) where mul x y := ⟨x.val * y.val⟩
instance : Div (UnitVal α) where div x y := ⟨x.val / y.val⟩
instance : Neg (UnitVal α) where neg x := ⟨-x.val⟩
instance : ToString (UnitVal n) where toString n := toString n.val

end UnitVal
end Time
end Std
