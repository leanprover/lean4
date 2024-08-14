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
def HourMarker.toAbsolute (marker : HourMarker) (time : Hour.Ordinal l) : Hour.Ordinal l :=
  match marker with
  | .am => time
  | .pm => by
    let mod := Int.mod_lt_of_pos (b := 24) (time.val + 12) (by decide)
    let l := time.property.left
    refine Bounded.LE.mk ((time.val + 12).mod 24) (And.intro ?_ ?_)
    · have h : 0 + 0 ≤ time.val + 12 := Int.add_le_add l (by decide)
      exact Int.mod_nonneg 24 h
    · split
      · exact Int.le_of_lt mod
      · exact Int.le_sub_one_of_lt mod
