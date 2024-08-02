/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.UnitVal
import Lean.Time.Bounded
import Lean.Time.LessEq
import Lean.Data.Rat
import Lean.Time.Date.Unit.Day
import Lean.Time.Date.Unit.Month

namespace Lean
namespace Date

set_option linter.all true

/-- Defines the enumeration for days of the week. Each variant corresponds to a day of the week,
from Monday to Sunday. -/
inductive Weekday
  /-- Monday. -/
  | mon
  /-- Tuesday. -/
  | tue
  /-- Wednesday. -/
  | wed
  /-- Thursday. -/
  | thu
  /-- Friday. -/
  | fri
  /-- Saturday. -/
  | sat
  /-- Sunday. -/
  | sun
  deriving Repr, Inhabited, BEq

namespace Weekday

/--
Converts a `Fin 7` representing a day index into a corresponding `Weekday`. This function is
useful for mapping numerical representations to days of the week.
-/
def ofFin : Fin 7 → Weekday
  | 0 => .mon
  | 1 => .tue
  | 2 => .wed
  | 3 => .thu
  | 4 => .fri
  | 5 => .sat
  | 6 => .sun

/--
Converts a `Weekday` to a `Nat`.
-/
def toNat : Weekday → Nat
  | .mon => 0
  | .tue => 1
  | .wed => 2
  | .thu => 3
  | .fri => 4
  | .sat => 5
  | .sun => 6

/--
Converts a `Weekday` to a `Fin`.
-/
def toFin : Weekday → Nat
  | .mon => 0
  | .tue => 1
  | .wed => 2
  | .thu => 3
  | .fri => 4
  | .sat => 5
  | .sun => 6

/--
Converts a `Nat` to a `Option Weekday`.
-/
def ofNat? : Nat → Option Weekday
  | 0 => some .mon
  | 1 => some .tue
  | 2 => some .wed
  | 3 => some .thu
  | 4 => some .fri
  | 5 => some .sat
  | 6 => some .sun
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
  | .mon => .sun
  | .tue => .mon
  | .wed => .tue
  | .thu => .wed
  | .fri => .thu
  | .sat => .fri
  | .sun => .sat
