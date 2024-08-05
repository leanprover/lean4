/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time.Basic

namespace Std
namespace Time
namespace Time

set_option linter.all true

/--
Represents a scalar value of time.
-/
structure Scalar where
  /--
  The quantity of seconds.
  -/
  second : Second.Offset
  /--
  The quantity of nanoseconds.
  -/
  nano : Nanosecond.Ordinal

namespace Scalar

/--
Converts the scalar value to seconds.
-/
def toSeconds (time : Scalar) : Second.Offset :=
  time.second

/--
Converts the scalar value to minutes.
-/
def toMinutes (time : Scalar) : Minute.Offset :=
  time.second.toMinutes

/--
Converts the scalar value to hours.
-/
def toHours (time : Scalar) : Hour.Offset :=
  time.second.toHours

end Scalar
end Time
end Time
