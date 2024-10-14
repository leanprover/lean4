/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Rat
import Std.Time.Date.Unit.Day

namespace Std
namespace Time
open Std.Internal
open Internal

set_option linter.all true

/--
Defines the enumeration for days of the week. Each variant corresponds to a day of the week.
-/
inductive Weekday
  /-- Sunday. -/
  | sunday

  /-- Monday. -/
  | monday

  /-- Tuesday. -/
  | tuesday

  /-- Wednesday. -/
  | wednesday

  /-- Thursday. -/
  | thursday

  /-- Friday. -/
  | friday

  /-- Saturday. -/
  | saturday
  deriving Repr, Inhabited, BEq

namespace Weekday

/--
`Ordinal` represents a bounded value for weekdays, which ranges between 1 and 7.
-/
def Ordinal := Bounded.LE 1 7

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 1 (1 + (6 : Nat))) n)

/--
Converts a `Ordinal` representing a day index into a corresponding `Weekday`. This function is useful
for mapping numerical representations to days of the week.
-/
def ofOrdinal : Ordinal → Weekday
  | 1 => .sunday
  | 2 => .monday
  | 3 => .tuesday
  | 4 => .wednesday
  | 5 => .thursday
  | 6 => .friday
  | 7 => .saturday

/--
Converts a `Weekday` to a `Ordinal`.
-/
def toOrdinal : Weekday → Ordinal
  | .sunday => 1
  | .monday => 2
  | .tuesday => 3
  | .wednesday => 4
  | .thursday => 5
  | .friday => 6
  | .saturday => 7

/--
Converts a `Weekday` to a `Nat`.
-/
def toNat : Weekday → Nat
  | .sunday => 1
  | .monday => 2
  | .tuesday => 3
  | .wednesday => 4
  | .thursday => 5
  | .friday => 6
  | .saturday => 7

/--
Converts a `Nat` to an `Option Weekday`.
-/
def ofNat? : Nat → Option Weekday
  | 1 => some .sunday
  | 2 => some .monday
  | 3 => some .tuesday
  | 4 => some .wednesday
  | 5 => some .thursday
  | 6 => some .friday
  | 7 => some .saturday
  | _ => none

/--
Converts a `Nat` to a `Weekday`. Panics if the value provided is invalid.
-/
@[inline]
def ofNat! (n : Nat) : Weekday :=
  match ofNat? n with
  | some res => res
  | none => panic! "invalid weekday"

/--
Gets the next `Weekday`.
-/
def next : Weekday → Weekday
  | .monday => .tuesday
  | .tuesday => .wednesday
  | .wednesday => .thursday
  | .thursday => .friday
  | .friday => .saturday
  | .saturday => .sunday
  | .sunday => .monday

/--
Check if it's a Weekend.
-/
def weekend : Weekday → Bool
  | .saturday => true
  | .sunday => true
  | _ => false

end Weekday
end Time
end Std
