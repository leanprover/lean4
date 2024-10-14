/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Init.Data.Range
import Std.Internal.Parsec
import Std.Internal.Parsec.ByteArray

import Std.Time.Internal.Bounded
import Std.Time.Format.Basic
import Std.Time.Time
import Std.Time.Date

namespace Std
namespace Time
namespace TimeZone
open Std.Internal.Parsec Std.Internal.Parsec.String

set_option linter.all true

/--
Represents a leap second entry with details such as the year, month, day, time, whether it's a positive leap second,
and a stationary string (presumably to capture additional information).
-/
structure LeapSecond where

  /--
  The timestamp when the leap second occurs.
  -/
  timestamp : Timestamp

  /--
  Indicates whether the leap second is positive (`true` for positive, `false` for negative).
  -/
  positive : Bool

  /--
  A string representing the stationary field, which could be used for additional information
  or metadata about the leap second.
  -/
  stationary : String

private def skipComment : Parser Unit := do
  skipChar '#'
  discard <| many (satisfy (· ≠ '\n'))
  discard ∘ optional <| skipChar '\n'
  return ()

private def failWith (opt : Option α) : Parser α :=
  match opt with
  | none => fail "invalid number"
  | some res => pure res

private def parseLeapSecond : Parser LeapSecond := do
  skipString "Leap"
  ws
  let year ← digits
  ws
  let month ← Std.Time.parseMonthShort
  ws
  let day ← digits
  ws

  let hour : Hour.Ordinal ← failWith =<< Internal.Bounded.ofInt? <$> digits
  skipChar ':'
  let minute : Minute.Ordinal ← failWith =<< Internal.Bounded.ofInt? <$> digits
  skipChar ':'
  let second : Second.Ordinal true ← failWith =<< Internal.Bounded.ofInt? <$> digits

  ws
  let positive ← (pchar '+' *> pure true)
  ws
  let stationary ← manyChars (satisfy Char.isAlpha)
  skipChar '\n'

  dbg_trace s!"{year}--{month}--{day}"

  let day ← failWith <| Internal.Bounded.ofInt? day
  let time : PlainTime ← failWith <| PlainTime.ofHourMinuteSeconds hour minute second
  let date : PlainDate ← failWith <| PlainDate.ofYearMonthDay (Year.Offset.ofNat year) month day
  let pdt := PlainDateTime.mk date time

  return { timestamp := pdt.toTimestampAssumingUTC, positive, stationary }

private def parseComments : Parser (Array Unit) :=
  many1 (ws *> skipComment)

/--
Parses a sequence of leap second entries.
-/
def parseLeapSeconds : Parser (Array LeapSecond) := do
  discard <| many (ws *> skipComment)
  let res ← many parseLeapSecond
  discard <| many (ws *> skipComment)
  eof
  return res
