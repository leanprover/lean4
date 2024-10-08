/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Init.Data.Int
import Std.Time.Time
import Std.Time.Date
import Std.Time.Duration

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
`Timestamp` represents a specific point in time since the UNIX Epoch.
-/
structure Timestamp where

  /--
  Duration since the unix epoch.
  -/
  val : Duration
  deriving Repr, BEq, Inhabited

instance : OfNat Timestamp n where
  ofNat := ⟨OfNat.ofNat n⟩

instance : ToString Timestamp where
  toString s := toString s.val

instance : Repr Timestamp where
  reprPrec s := reprPrec (toString s)

/--
Type class to transform to `Timestamp`. It's used internally to generate timestamps out of
some absolute date types.
-/
class ToTimestamp (α : Type) where
  /--
  Transforms into a `Timestamp`.
  -/
  toTimestamp : α → Timestamp

instance : ToTimestamp Timestamp where
  toTimestamp := id

namespace Timestamp

/--
Fetches the current duration from the system.
-/
@[extern "lean_get_current_time"]
opaque now : IO Timestamp

/--
Converts a `Timestamp` to a `Minute.Offset`
-/
def toMinutes (tm : Timestamp) : Minute.Offset :=
  tm.val.second.ediv 60

/--
Converts a `Timestamp` to a `Day.Offset`
-/
def toDays (tm : Timestamp) : Day.Offset :=
  tm.val.second.ediv 86400

/--
Creates a new `Timestamp` out of `Second.Offset`.
-/
def ofSecondsSinceUnixEpoch (secs : Second.Offset) : Timestamp :=
  ⟨Duration.ofSeconds secs⟩

/--
Creates a new `Timestamp` out of `Nanosecond.Offset`.
-/
def ofNanosecondsSinceUnixEpoch (secs : Nanosecond.Offset) : Timestamp :=
  ⟨Duration.ofNanoseconds secs⟩

/--
Converts a `Timestamp` into its equivalent `Second.Offset`.
-/
@[inline]
def toSecondsSinceUnixEpoch (t : Timestamp) : Second.Offset :=
  t.val.second

/--
Converts a `Timestamp` from a `Nanosecond.Offset`
-/
@[inline]
def toNanosecondsSinceUnixEpoch (tm : Timestamp) : Nanosecond.Offset :=
  let nanos := tm.toSecondsSinceUnixEpoch.mul 1000000000
  let nanos := nanos + (.ofInt tm.val.nano.val)
  nanos

/--
Calculates a `Timestamp` out of two `Timestamp`s.
-/
@[inline]
def since (f : Timestamp) : IO Duration := do
  let cur ← Timestamp.now
  return Std.Time.Duration.sub cur.val f.val

/--
Creates a duration out of the `Timestamp` since the unix epoch.
-/
@[inline]
def toDurationSinceUnixEpoch (tm : Timestamp) : Duration :=
  tm.val

/--
Adds a `Nanosecond.Offset` to a `Timestamp`
-/
@[inline]
def addNanoseconds (t : Timestamp) (s : Nanosecond.Offset) : Timestamp :=
  ⟨t.val + s⟩

/--
Adds a `Nanosecond.Offset` to a `Timestamp`
-/
@[inline]
def subNanoseconds (t : Timestamp) (s : Nanosecond.Offset) : Timestamp :=
  ⟨t.val - s⟩

/--
Adds a `Second.Offset` to a `Timestamp`
-/
@[inline]
def addSeconds (t : Timestamp) (s : Second.Offset) : Timestamp :=
  ⟨t.val + s⟩

/--
Subtracts a `Second.Offset` from a `Timestamp`
-/
@[inline]
def subSeconds (t : Timestamp) (s : Second.Offset) : Timestamp :=
  ⟨t.val - s⟩

/--
Adds a `Minute.Offset` to a `Timestamp`
-/
@[inline]
def addMinutes (t : Timestamp) (m : Minute.Offset) : Timestamp :=
  ⟨t.val + m⟩

/--
Subtracts a `Minute.Offset` from a `Timestamp`
-/
@[inline]
def subMinutes (t : Timestamp) (m : Minute.Offset) : Timestamp :=
  ⟨t.val - m⟩

/--
Adds an `Hour.Offset` to a `Timestamp`
-/
@[inline]
def addHours (t : Timestamp) (h : Hour.Offset) : Timestamp :=
  ⟨t.val + h⟩

/--
Subtracts an `Hour.Offset` from a `Timestamp`
-/
@[inline]
def subHours (t : Timestamp) (h : Hour.Offset) : Timestamp :=
  ⟨t.val - h⟩

/--
Adds a `Day.Offset` to a `Timestamp`
-/
@[inline]
def addDays (t : Timestamp) (d : Day.Offset) : Timestamp :=
  ⟨t.val + d⟩

/--
Subtracts a `Day.Offset` from a `Timestamp`
-/
@[inline]
def subDays (t : Timestamp) (d : Day.Offset) : Timestamp :=
  ⟨t.val - d⟩

/--
Adds a `Week.Offset` to a `Timestamp`
-/
@[inline]
def addWeeks (t : Timestamp) (d : Week.Offset) : Timestamp :=
  ⟨t.val + d⟩

/--
Subtracts a `Week.Offset` from a `Timestamp`
-/
@[inline]
def subWeeks (t : Timestamp) (d : Week.Offset) : Timestamp :=
  ⟨t.val - d⟩

instance : HAdd Timestamp Duration Timestamp where
  hAdd x y := ⟨x.val + y⟩

instance : HAdd Timestamp Day.Offset Timestamp where
  hAdd := addDays

instance : HSub Timestamp Day.Offset Timestamp where
  hSub := subDays

instance : HAdd Timestamp Week.Offset Timestamp where
  hAdd := addWeeks

instance : HSub Timestamp Week.Offset Timestamp where
  hSub := subWeeks

instance : HAdd Timestamp Hour.Offset Timestamp where
  hAdd := addHours

instance : HSub Timestamp Hour.Offset Timestamp where
  hSub := subHours

instance : HAdd Timestamp Minute.Offset Timestamp where
  hAdd := addMinutes

instance : HSub Timestamp Minute.Offset Timestamp where
  hSub := subMinutes

instance : HAdd Timestamp Second.Offset Timestamp where
  hAdd := addSeconds

instance : HSub Timestamp Second.Offset Timestamp where
  hSub := subSeconds

instance : HAdd Timestamp Nanosecond.Offset Timestamp where
  hAdd := addNanoseconds

instance : HSub Timestamp Nanosecond.Offset Timestamp where
  hSub := subNanoseconds

instance : HSub Timestamp Timestamp Duration where
  hSub x y := x.val - y.val

end Timestamp
