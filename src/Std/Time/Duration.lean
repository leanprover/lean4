/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Bounded
import Std.Time.Time

namespace Std
namespace Time

/--
`Instant` represents a place in time with second and nanoseconds precision.
-/
structure Instant where
  second : Second.Offset
  nano : Nanosecond.Ordinal
  valid : second.val ≥ 0 ∧ nano.val ≥ 0
  deriving Repr

/--
Time duration with nanosecond precision. This type allows negative duration.
-/
structure Duration where
  second : Second.Offset
  nano : Nanosecond.Span

namespace Instant

/--
Gets the difference of two `Instant` in a `Duration`.
-/
def sub (t₁ t₂ : Instant) : Duration :=
  let nsec_diff := (t₁.nano).subBounds (t₂.nano)
  let sec_diff := (t₁.second) - (t₂.second)
  if h : sec_diff.val > 0 ∧ nsec_diff.val ≤ -1 then
    let truncated := nsec_diff.truncateTop h.right
    { second := (sec_diff - 1), nano := truncated.addTop 1000000000 }
  else if h₁ : sec_diff.val < 0 ∧ nsec_diff.val ≥ 1 then
    let truncated := nsec_diff.truncateBottom h₁.right
    { second := (sec_diff + 1), nano := (truncated.subBottom 1000000000) }
  else
    { second := sec_diff, nano := nsec_diff }

instance : HSub Instant Instant Duration where
  hSub := Instant.sub

/--
Gets how much time elapsed since another `Instant` and returns a `Duration`.
-/
@[inline]
def since (instant : Instant) (since : Instant) : Duration :=
  Instant.sub since instant

end Instant

namespace Duration

/--
Returns a `Duration` representing the given number of second.
-/
def ofSeconds (second : Second.Offset) : Duration :=
  { second := second, nano := Bounded.LE.mk 0 (by decide) }

/--
Returns a `Duration` representing the given number of minute.
-/
def ofMinutes (minute : Minute.Offset) : Duration :=
  { second := minute.toSeconds * 60, nano := Bounded.LE.mk 0 (by decide) }

/--
Returns a `Duration` representing the given number of hour.
-/
def ofHours (hour : Hour.Offset) : Duration :=
  { second := hour.toSeconds * 3600, nano := Bounded.LE.mk 0 (by decide) }

end Duration
