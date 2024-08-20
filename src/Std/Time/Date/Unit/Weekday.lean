/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Data.Rat
import Std.Time.Date.Unit.Day

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Defines the enumeration for days of the week. Each variant corresponds to a day of the week, from Monday to Sunday.
-/
inductive Weekday
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
  /-- Sunday. -/
  | sunday
  deriving Repr, Inhabited, BEq

namespace Weekday

/--
Converts a `Fin 7` representing a day index into a corresponding `Weekday`. This function is useful
for mapping numerical representations to days of the week.
-/
def ofFin : Fin 7 → Weekday
  | 0 => .monday
  | 1 => .tuesday
  | 2 => .wednesday
  | 3 => .thursday
  | 4 => .friday
  | 5 => .saturday
  | 6 => .sunday

/--
Converts a `Weekday` to a `Nat`.
-/
def toNat : Weekday → Nat
  | .monday => 0
  | .tuesday => 1
  | .wednesday => 2
  | .thursday => 3
  | .friday => 4
  | .saturday => 5
  | .sunday => 6

/--
Converts a `Weekday` to a `Fin`.
-/
def toFin : Weekday → Nat
  | .monday => 0
  | .tuesday => 1
  | .wednesday => 2
  | .thursday => 3
  | .friday => 4
  | .saturday => 5
  | .sunday => 6

/--
Converts a `Nat` to an `Option Weekday`.
-/
def ofNat? : Nat → Option Weekday
  | 0 => some .monday
  | 1 => some .tuesday
  | 2 => some .wednesday
  | 3 => some .thursday
  | 4 => some .friday
  | 5 => some .saturday
  | 6 => some .sunday
  | _ => none

/--
Converts a `Nat` to a `Weekday`. Panics if the value provided is invalid.
-/
@[inline]
def ofNat! (n : Nat) : Weekday :=
  match ofNat? n with
  | some res => res
  | none     => panic! "invalid weekday"

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
