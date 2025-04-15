/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Init.System.IO
import Std.Time.Time
import Std.Time.Date
import Std.Time.Duration

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Represents an exact point in time as a UNIX Epoch timestamp.
-/
@[ext]
structure Timestamp where

  /--
  Duration since the unix epoch.
  -/
  val : Duration
deriving Repr, DecidableEq, Inhabited

instance : LE Timestamp where
  le x y := x.val ≤ y.val

instance { x y : Timestamp } : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance : OfNat Timestamp n where
  ofNat := ⟨OfNat.ofNat n⟩

instance : ToString Timestamp where
  toString s := toString s.val.toSeconds

instance : Repr Timestamp where
  reprPrec s := Repr.addAppParen ("Timestamp.ofNanosecondsSinceUnixEpoch " ++ repr s.val.toNanoseconds)

instance : Ord Timestamp where
  compare := compareOn (·.val)

theorem Timestamp.compare_def :
    compare (α := Timestamp) = compareOn (·.val) := rfl

instance : TransOrd Timestamp := inferInstanceAs <| TransCmp (compareOn _)

instance : LawfulEqOrd Timestamp where
  eq_of_compare {a b} h := by
    simp only [Timestamp.compare_def] at h
    apply Timestamp.ext
    exact LawfulEqOrd.eq_of_compare h

namespace Timestamp

/--
Fetches the current duration from the system.
-/
@[extern "lean_get_current_time"]
opaque now : IO Timestamp

/--
Converts a `Timestamp` to minutes as `Minute.Offset`.
-/
@[inline]
def toMinutes (tm : Timestamp) : Minute.Offset :=
  tm.val.second.ediv 60

/--
Converts a `Timestamp` to days as `Day.Offset`.
-/
@[inline]
def toDays (tm : Timestamp) : Day.Offset :=
  tm.val.second.ediv 86400

/--
Creates a `Timestamp` from a `Second.Offset` since the Unix epoch.
-/
@[inline]
def ofSecondsSinceUnixEpoch (secs : Second.Offset) : Timestamp :=
  ⟨Duration.ofSeconds secs⟩

/--
Creates a `Timestamp` from a `Nanosecond.Offset` since the Unix epoch.
-/
@[inline]
def ofNanosecondsSinceUnixEpoch (nanos : Nanosecond.Offset) : Timestamp :=
  ⟨Duration.ofNanoseconds nanos⟩

/--
Creates a `Timestamp` from a `Millisecond.Offset` since the Unix epoch.
-/
@[inline]
def ofMillisecondsSinceUnixEpoch (milli : Millisecond.Offset) : Timestamp :=
  ⟨Duration.ofNanoseconds milli.toNanoseconds⟩

/--
Converts a `Timestamp` to seconds as `Second.Offset`.
-/
@[inline]
def toSecondsSinceUnixEpoch (t : Timestamp) : Second.Offset :=
  t.val.second

/--
Converts a `Timestamp` to nanoseconds as `Nanosecond.Offset`.
-/
@[inline]
def toNanosecondsSinceUnixEpoch (tm : Timestamp) : Nanosecond.Offset :=
  let nanos := tm.toSecondsSinceUnixEpoch.mul 1000000000
  let nanos := nanos + (.ofInt tm.val.nano.val)
  nanos

/--
Converts a `Timestamp` to nanoseconds as `Millisecond.Offset`.
-/
@[inline]
def toMillisecondsSinceUnixEpoch (tm : Timestamp) : Millisecond.Offset :=
  tm.toNanosecondsSinceUnixEpoch.toMilliseconds

/--
Calculates the duration from the given `Timestamp` to the current time.
-/
@[inline]
def since (f : Timestamp) : IO Duration := do
  let cur ← Timestamp.now
  return Std.Time.Duration.sub cur.val f.val

/--
Returns the `Duration` represented by the `Timestamp` since the Unix epoch.
-/
@[inline]
def toDurationSinceUnixEpoch (tm : Timestamp) : Duration :=
  tm.val

/--
Adds a `Millisecond.Offset` to the given `Timestamp`.
-/
@[inline]
def addMilliseconds (t : Timestamp) (s : Millisecond.Offset) : Timestamp :=
  ⟨t.val + s⟩

/--
Subtracts a `Millisecond.Offset` from the given `Timestamp`.
-/
@[inline]
def subMilliseconds (t : Timestamp) (s : Millisecond.Offset) : Timestamp :=
  ⟨t.val - s⟩

/--
Adds a `Nanosecond.Offset` to the given `Timestamp`.
-/
@[inline]
def addNanoseconds (t : Timestamp) (s : Nanosecond.Offset) : Timestamp :=
  ⟨t.val + s⟩

/--
Subtracts a `Nanosecond.Offset` from the given `Timestamp`.
-/
@[inline]
def subNanoseconds (t : Timestamp) (s : Nanosecond.Offset) : Timestamp :=
  ⟨t.val - s⟩

/--
Adds a `Second.Offset` to the given `Timestamp`.
-/
@[inline]
def addSeconds (t : Timestamp) (s : Second.Offset) : Timestamp :=
  ⟨t.val + s⟩

/--
Subtracts a `Second.Offset` from the given `Timestamp`.
-/
@[inline]
def subSeconds (t : Timestamp) (s : Second.Offset) : Timestamp :=
  ⟨t.val - s⟩

/--
Adds a `Minute.Offset` to the given `Timestamp`.
-/
@[inline]
def addMinutes (t : Timestamp) (m : Minute.Offset) : Timestamp :=
  ⟨t.val + m⟩

/--
Subtracts a `Minute.Offset` from the given `Timestamp`.
-/
@[inline]
def subMinutes (t : Timestamp) (m : Minute.Offset) : Timestamp :=
  ⟨t.val - m⟩

/--
Adds an `Hour.Offset` to the given `Timestamp`.
-/
@[inline]
def addHours (t : Timestamp) (h : Hour.Offset) : Timestamp :=
  ⟨t.val + h⟩

/--
Subtracts an `Hour.Offset` from the given `Timestamp`.
-/
@[inline]
def subHours (t : Timestamp) (h : Hour.Offset) : Timestamp :=
  ⟨t.val - h⟩

/--
Adds a `Day.Offset` to the given `Timestamp`.
-/
@[inline]
def addDays (t : Timestamp) (d : Day.Offset) : Timestamp :=
  ⟨t.val + d⟩

/--
Subtracts a `Day.Offset` from the given `Timestamp`.
-/
@[inline]
def subDays (t : Timestamp) (d : Day.Offset) : Timestamp :=
  ⟨t.val - d⟩

/--
Adds a `Week.Offset` to the given `Timestamp`.
-/
@[inline]
def addWeeks (t : Timestamp) (d : Week.Offset) : Timestamp :=
  ⟨t.val + d⟩

/--
Subtracts a `Week.Offset` from the given `Timestamp`.
-/
@[inline]
def subWeeks (t : Timestamp) (d : Week.Offset) : Timestamp :=
  ⟨t.val - d⟩

/--
Adds a `Duration` to the given `Timestamp`.
-/
@[inline]
def addDuration (t : Timestamp) (d : Duration) : Timestamp :=
  ⟨t.val + d⟩

/--
Subtracts a `Duration` from the given `Timestamp`.
-/
@[inline]
def subDuration (t : Timestamp) (d : Duration) : Timestamp :=
  ⟨t.val - d⟩

instance : HAdd Timestamp Duration Timestamp where
  hAdd := addDuration

instance : HSub Timestamp Duration Timestamp where
  hSub := subDuration

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

instance : HAdd Timestamp Millisecond.Offset Timestamp where
  hAdd := addMilliseconds

instance : HSub Timestamp Millisecond.Offset Timestamp where
  hSub := subMilliseconds

instance : HAdd Timestamp Nanosecond.Offset Timestamp where
  hAdd := addNanoseconds

instance : HSub Timestamp Nanosecond.Offset Timestamp where
  hSub := subNanoseconds

instance : HSub Timestamp Timestamp Duration where
  hSub x y := x.val - y.val

end Timestamp
