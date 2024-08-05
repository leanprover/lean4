/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Bounded

namespace Std
namespace Time

set_option linter.all true

/--
A `Sign` is a type that can have three values -1, 0 and 1 that represents the sign of a value.
-/
def Sign := Bounded.LE (-1) 1

instance : ToString Sign where
  toString
    | ⟨-1, _⟩ => "-"
    | _ => "+"

namespace Sign

/--
Gets the `Sign` out of a integer.
-/
@[inline]
def ofInt (val : Int) : Sign := by
  refine ⟨val.sign, ?_⟩
  simp [Int.sign]
  split <;> simp

/--
Applies the sign to a value.
-/
@[inline]
def apply (sign : Sign) (val : Int) : Int :=
  val * sign.val

end Sign
end Time
end Std
