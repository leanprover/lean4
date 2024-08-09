/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time.Basic

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
`HourMarker` represents the two 12-hour periods of the day: `am` for hour between 12:00 AM and
11:59 AM, and `pm` for hour between 12:00 PM and 11:59 PM.
-/
inductive HourMarker
  /-- Ante meridiem. -/
  | am
  /-- Post meridiem. -/
  | pm

/--
Converts a 12-hour clock time to a 24-hour clock time based on the `HourMarker`.
-/
def HourMarker.toAbsolute (marker : HourMarker) (time : Hour.Ordinal) (h₀ : time.toInt ≤ 12) : Hour.Ordinal :=
  match marker with
  | .am => time
  | .pm => Bounded.LE.mk (time.toInt + 12) (And.intro (Int.add_le_add (c := 0) time.property.left (by decide)) (Int.add_le_add_right h₀ 12))

/--
Converts a 12-hour clock time to a 24-hour clock time based on the `HourMarker` without a proof.
-/
def HourMarker.toAbsoluteShift (marker : HourMarker) (time : Hour.Ordinal) : Hour.Ordinal :=
  match marker with
  | .am => time
  | .pm => Bounded.LE.ofFin (Fin.ofNat (time.val.toNat + 12))
