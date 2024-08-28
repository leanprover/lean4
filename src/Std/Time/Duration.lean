/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.DateTime
import Std.Time.Zoned

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Duration is just a period between two timestamps.
-/
def Duration := Timestamp
  deriving Repr, BEq

instance : ToString Duration where
  toString s :=
    let (sign, secs, nanos) :=
      if s.second.val > 0 then ("" ,s.second.val, s.nano.val)
      else if s.second.val < 0 then ("-", -s.second.val, -s.nano.val)
      else if s.nano.val < 0 then ("-", -s.second.val, -s.nano.val) else ("", s.second.val, s.nano.val)
    sign ++ toString secs ++ "." ++ toString nanos ++ "s"

instance : Repr Duration where
  reprPrec s := reprPrec (toString s)

namespace Duration

/--
Creates a new `Duration` out of `Second.Offset`.
-/
def ofSeconds (secs : Second.Offset) : Duration :=
  Timestamp.ofSecondsSinceUnixEpoch secs

/--
Creates a new `Duration` out of `Nanosecond.Offset`.
-/
def ofNanosecond (secs : Nanosecond.Offset) : Duration :=
  Timestamp.ofNanosecondsSinceUnixEpoch secs

/--
Calculates a `Duration` out of two `Timestamp`s.
-/
def since (f : Timestamp) : IO Duration := do
  let cur ← Timestamp.now
  return Std.Time.Timestamp.sub cur f

/--
Adds a `Duration` to a `Timestamp`.
-/
def add (f : Timestamp) (d : Duration) : Timestamp :=
  Std.Time.Timestamp.add f d

/--
Checks if the duration is zero seconds ands zero nanoseconds.
-/
def isZero (d : Duration) : Bool :=
  d.second.val = 0 ∧ d.nano.val = 0

instance : HAdd Timestamp Duration Timestamp where
  hAdd := add

instance : HSub Timestamp Timestamp Duration where
  hSub := Std.Time.Timestamp.sub

end Duration

namespace PlainDate

/--
Calculates the duration between a given `PlainDate` and a specified date.
-/
def since [ToTimestamp α] (date : PlainDate) (since : α) : Duration :=
  let date  := date.toTimestamp
  let since := ToTimestamp.toTimestamp since
  Std.Time.Timestamp.sub date since

end PlainDate

namespace PlainDateTime

/--
Calculates the duration between a given `PlainDateTime` and a specified date.
-/
def since [ToTimestamp α] (date : PlainDateTime) (since : α) : Duration :=
  let date  := date.toTimestamp
  let since := ToTimestamp.toTimestamp since
  Std.Time.Timestamp.sub date since

end PlainDateTime

namespace DateTime

/--
Calculates the duration between a given `DateTime` and a specified date.
-/
def since [ToTimestamp α] (date : DateTime tz) (since : α) : Duration :=
  let date  := date.toTimestamp
  let since := ToTimestamp.toTimestamp since
  Std.Time.Timestamp.sub date since

end DateTime

namespace ZonedDateTime

/--
Calculates the duration between a given `ZonedDateTime` and a specified date.
-/
def since [ToTimestamp α] (date : ZonedDateTime) (since : α) : Duration :=
  let date  := date.toTimestamp
  let since := ToTimestamp.toTimestamp since
  Std.Time.Timestamp.sub date since

end ZonedDateTime
