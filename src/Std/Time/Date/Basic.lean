/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Date.Unit.Basic
import Std.Time.Date.ValidDate
import Std.Time.Time.Basic

namespace Std
namespace Time

namespace Nanosecond
namespace Offset

/--
Convert `Nanosecond.Offset` into `Day.Offset`.
-/
@[inline]
def toDays (nanoseconds : Nanosecond.Offset) : Day.Offset :=
  nanoseconds.div 86400000000000

/--
Convert `Day.Offset` into `Nanosecond.Offset`.
-/
@[inline]
def ofDays (days : Day.Offset) : Nanosecond.Offset :=
  days.mul 86400000000000

/--
Convert `Nanosecond.Offset` into `Week.Offset`.
-/
@[inline]
def toWeeks (nanoseconds : Nanosecond.Offset) : Week.Offset :=
  nanoseconds.div 604800000000000

/--
Convert `Week.Offset` into `Nanosecond.Offset`.
-/
@[inline]
def ofWeeks (weeks : Week.Offset) : Nanosecond.Offset :=
  weeks.mul 604800000000000

end Offset
end Nanosecond

namespace Millisecond
namespace Offset

/--
Convert `Millisecond.Offset` into `Day.Offset`.
-/
@[inline]
def toDays (milliseconds : Millisecond.Offset) : Day.Offset :=
  milliseconds.div 86400000

/--
Convert `Day.Offset` into `Millisecond.Offset`.
-/
@[inline]
def ofDays (days : Day.Offset) : Millisecond.Offset :=
  days.mul 86400000

/--
Convert `Millisecond.Offset` into `Week.Offset`.
-/
@[inline]
def toWeeks (milliseconds : Millisecond.Offset) : Week.Offset :=
  milliseconds.div 604800000

/--
Convert `Week.Offset` into `Millisecond.Offset`.
-/
@[inline]
def ofWeeks (weeks : Week.Offset) : Millisecond.Offset :=
  weeks.mul 604800000

end Offset
end Millisecond

namespace Second
namespace Offset

/--
Convert `Second.Offset` into `Day.Offset`.
-/
@[inline]
def toDays (seconds : Second.Offset) : Day.Offset :=
  seconds.div 86400

/--
Convert `Day.Offset` into `Second.Offset`.
-/
@[inline]
def ofDays (days : Day.Offset) : Second.Offset :=
  days.mul 86400

/--
Convert `Second.Offset` into `Week.Offset`.
-/
@[inline]
def toWeeks (seconds : Second.Offset) : Week.Offset :=
  seconds.div 604800

/--
Convert `Week.Offset` into `Second.Offset`.
-/
@[inline]
def ofWeeks (weeks : Week.Offset) : Second.Offset :=
  weeks.mul 604800

end Offset
end Second

namespace Minute
namespace Offset

/--
Convert `Minute.Offset` into `Day.Offset`.
-/
@[inline]
def toDays (minutes : Minute.Offset) : Day.Offset :=
  minutes.div 1440

/--
Convert `Day.Offset` into `Minute.Offset`.
-/
@[inline]
def ofDays (days : Day.Offset) : Minute.Offset :=
  days.mul 1440

/--
Convert `Minute.Offset` into `Week.Offset`.
-/
@[inline]
def toWeeks (minutes : Minute.Offset) : Week.Offset :=
  minutes.div 10080

/--
Convert `Week.Offset` into `Minute.Offset`.
-/
@[inline]
def ofWeeks (weeks : Week.Offset) : Minute.Offset :=
  weeks.mul 10080

end Offset
end Minute

namespace Hour
namespace Offset

/--
Convert `Hour.Offset` into `Day.Offset`.
-/
@[inline]
def toDays (hours : Hour.Offset) : Day.Offset :=
  hours.div 24

/--
Convert `Day.Offset` into `Hour.Offset`.
-/
@[inline]
def ofDays (days : Day.Offset) : Hour.Offset :=
  days.mul 24

/--
Convert `Hour.Offset` into `Week.Offset`.
-/
@[inline]
def toWeeks (hours : Hour.Offset) : Week.Offset :=
  hours.div 168

/--
Convert `Week.Offset` into `Hour.Offset`.
-/
@[inline]
def ofWeeks (weeks : Week.Offset) : Hour.Offset :=
  weeks.mul 168

end Offset
end Hour
