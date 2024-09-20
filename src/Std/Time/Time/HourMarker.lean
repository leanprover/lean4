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
`HourMarker` represents the two 12-hour periods of the day: `am` for hours between 12:00 AM and
11:59 AM, and `pm` for hours between 12:00 PM and 11:59 PM.
-/
inductive HourMarker
  /-- Ante meridiem. -/
  | am
  /-- Post meridiem. -/
  | pm
  deriving Repr, BEq

namespace HourMarker

/--
`ofOrdinal` converts an `Hour.Ordinal` value to an `HourMarker`, indicating whether it is AM or PM.
-/
def ofOrdinal (time : Hour.Ordinal) : HourMarker :=
  if time.val ≥ 12 then
    .pm
  else
    .am

/--
Converts a 12-hour clock time to a 24-hour clock time based on the `HourMarker`.
-/
def toAbsolute (marker : HourMarker) (time : Bounded.LE 1 12) : Hour.Ordinal :=
  match marker with
  | .am => time.sub 1 |>.expandTop (by decide)
  | .pm => time.add 11 |>.emod 24 (by decide)

end HourMarker
end Time
end Std
