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
11:59 AM, and `pm` for hours between 12:00 PM and 11:59 PM.
-/
inductive HourMarker
  /-- Ante meridiem. -/
  | am
  /-- Post meridiem. -/
  | pm

/--
Converts a 12-hour clock time to a 24-hour clock time based on the `HourMarker`.
-/
def HourMarker.toAbsolute (marker : HourMarker) (time : Bounded.LE 0 12) : Hour.Ordinal l :=
  match marker with
  | .am => by
    refine time.expandTop ?_
    split <;> decide
  | .pm => by
    have time := time.add 12 |>.emod 24 (by decide)
    cases l
    · exact time
    · exact time.expandTop (by decide)
