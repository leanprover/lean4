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
deriving Repr, Inhabited, DecidableEq

namespace Weekday

/--
`Ordinal` represents a bounded value for weekdays, which ranges between 1 and 7.
-/
def Ordinal := Bounded.LE 1 7
deriving Repr, DecidableEq, LT, LE

instance {x y : Ordinal} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Ordinal} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 1 (1 + (6 : Nat))) n)

instance : Inhabited Ordinal where
  default := 1

instance : Ord Ordinal := inferInstanceAs <| Ord (Bounded.LE 1 _)

instance : TransOrd Ordinal := inferInstanceAs <| TransOrd (Bounded.LE 1 _)

instance : LawfulEqOrd Ordinal := inferInstanceAs <| LawfulEqOrd (Bounded.LE 1 _)

/--
Converts a `Ordinal` representing a day index into a corresponding `Weekday`. This function is useful
for mapping numerical representations to days of the week.
-/
def ofOrdinal : Ordinal → Weekday
  | 1 => .monday
  | 2 => .tuesday
  | 3 => .wednesday
  | 4 => .thursday
  | 5 => .friday
  | 6 => .saturday
  | 7 => .sunday

/--
Converts a `Weekday` to a `Ordinal`.
-/
def toOrdinal : Weekday → Ordinal
  | .monday => 1
  | .tuesday => 2
  | .wednesday => 3
  | .thursday => 4
  | .friday => 5
  | .saturday => 6
  | .sunday => 7

instance : Ord Weekday where
  compare := compareOn toOrdinal

instance : TransOrd Weekday := inferInstanceAs <| TransCmp (compareOn toOrdinal)

theorem toOrdinal.inj {a b : Weekday} (h : toOrdinal a = toOrdinal b) : a = b := by
  cases a <;> cases b <;> rw [toOrdinal] at * <;> contradiction

instance : LawfulEqOrd Weekday where
  eq_of_compare := toOrdinal.inj ∘ LawfulEqOrd.eq_of_compare (α := Ordinal)

/--
Converts a `Weekday` to a `Nat`.
-/
def toNat : Weekday → Nat
  | .monday => 1
  | .tuesday => 2
  | .wednesday => 3
  | .thursday => 4
  | .friday => 5
  | .saturday => 6
  | .sunday => 7

/--
Converts a `Nat` to an `Option Weekday`.
-/
def ofNat? : Nat → Option Weekday
  | 1 => some .monday
  | 2 => some .tuesday
  | 3 => some .wednesday
  | 4 => some .thursday
  | 5 => some .friday
  | 6 => some .saturday
  | 7 => some .sunday
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
Check if it's a weekend.
-/
def isWeekend : Weekday → Bool
  | .saturday => true
  | .sunday => true
  | _ => false

end Weekday
end Time
end Std
