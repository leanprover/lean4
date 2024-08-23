/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.DateTime.Timestamp
import Std.Time.DateTime.LocalDateTime

namespace Std
namespace Time
namespace Timestamp

set_option linter.all true

/--
Converts a `LocalDateTime` to a `Timestamp`
-/
@[inline]
def ofLocalDateTime (ldt : LocalDateTime) : Timestamp :=
  ldt.toLocalTimestamp

/--
Converts a `Timestamp` to a `LocalDateTime`
-/
@[inline]
def toLocalDateTime (timestamp : Timestamp) : LocalDateTime :=
  LocalDateTime.ofUTCTimestamp timestamp

/--
Converts a `LocalDate` to a `Timestamp`
-/
@[inline]
def ofLocalDate (ld : LocalDate) : Timestamp :=
  let days := ld.toDaysSinceUNIXEpoch
  let secs := days.toSeconds
  Timestamp.ofSecondsSinceUnixEpoch secs

/--
Converts a `Timestamp` to a `LocalDate`
-/
@[inline]
def toLocalDate (timestamp : Timestamp) : LocalDate :=
  let secs := timestamp.toSeconds
  let days := Day.Offset.ofSeconds secs
  LocalDate.ofDaysSinceUNIXEpoch days

/--
Converts a `LocalTime` to a `Timestamp`
-/
@[inline]
def ofLocalTime (lt : LocalTime) : Timestamp :=
  let nanos := lt.toNanoseconds
  Timestamp.ofNanosecondsSinceUnixEpoch nanos

/--
Converts a `Timestamp` to a `LocalTime`
-/
@[inline]
def toLocalTime (timestamp : Timestamp) : LocalTime :=
  let nanos := timestamp.toNanosecondsSinceUnixEpoch
  LocalTime.ofNanoseconds nanos

end Timestamp

namespace LocalDateTime

/--
Converts a `LocalDate` to a `Timestamp`
-/
@[inline]
def ofLocalDate (ld : LocalDate) : LocalDateTime :=
  LocalDateTime.ofUTCTimestamp (Timestamp.ofLocalDate ld)

/--
Converts a `LocalDateTime` to a `LocalDate`
-/
@[inline]
def toLocalDate (ldt : LocalDateTime) : LocalDate :=
  Timestamp.toLocalDate ldt.toLocalTimestamp

/--
Converts a `LocalTime` to a `LocalDateTime`
-/
@[inline]
def ofLocalTime (lt : LocalTime) : LocalDateTime :=
  LocalDateTime.ofUTCTimestamp (Timestamp.ofLocalTime lt)

/--
Converts a `LocalDateTime` to a `LocalTime`
-/
@[inline]
def toLocalTime (ldt : LocalDateTime) : LocalTime :=
  Timestamp.toLocalTime ldt.toLocalTimestamp

end LocalDateTime
