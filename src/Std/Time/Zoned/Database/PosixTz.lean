/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Parsec
public import Std.Time.Zoned.ZoneRules

/-!
POSIX TZ string parser for RFC 8536 §3.3 footer strings.
-/

public section

namespace Std.Time.TimeZone
open Std.Time.Internal

set_option linter.all true

open Std.Internal.Parsec Std.Internal.Parsec.String

-- Parse digits and validate them into a Bounded.LE type, with an optional extra predicate.
private def parseBoundedNat {lo hi : Int} (name : String) (extra : Int → Bool := fun _ => true) : Parser (Bounded.LE lo hi) := do
  let n ← Int.ofNat <$> digits
  if !extra n then fail s!"{name} {n} out of range"

  match Bounded.LE.ofInt n with
  | some b => pure b
  | none => fail s!"{name} {n} out of range"

private def posixParseSign : Parser Int :=
  attempt (pchar '-' *> pure (-1 : Int))
  <|> attempt (pchar '+' *> pure 1)
  <|> pure 1

-- <time> ::= <hour> [":" <minute> [":" <second>]]
-- `maxHour` caps the hour field; POSIX requires 0–24, extended mode allows 0–167.
private def posixParseHMS (maxHour : Nat := 24) : Parser Second.Offset := do
  let rawH ← digits
  if rawH > maxHour then fail s!"hour {rawH} out of range 0-{maxHour}"

  let h : Bounded.LE 0 167 ← match Bounded.LE.ofNat? rawH with
    | some b => pure b
    | none   => fail s!"hour {rawH} out of range 0-{167}"

  let m : Minute.Ordinal ← attempt (pchar ':' *> parseBoundedNat "minute") <|> pure (Bounded.LE.mk 0 (by decide))
  let s : Second.Ordinal false ← attempt (pchar ':' *> parseBoundedNat "second") <|> pure (Bounded.LE.mk 0 (by decide))
  return (Hour.Offset.ofInt h.val).toSeconds + m.toOffset.toSeconds + s.toOffset

-- <offset> ::= [ "+" | "-" ] <time>
private def posixParseOffset : Parser TimeZone.Offset := do
  let sign ← posixParseSign
  let secs ← posixParseHMS

  -- POSIX offsets are west-positive, so we negate
  return ⟨Second.Offset.ofInt (-sign * secs.val)⟩

-- <quoted-name> ::= "<" <quoted-char> { <quoted-char> } ">"
private def quotedName : Parser String :=
  manyChars (satisfy (fun c => Char.isAlphanum c ∨ c == '+' ∨ c == '-'))

-- <tzname> ::= <alpha>{3,} | "<" <char>+ ">"
private def posixParseName : Parser String := do
  if (← peek?) == some '<'
    then skip *> quotedName <* attempt (pchar '>')
    else manyChars asciiLetter

-- "M" <month> "." <week> "." <weekday>
private def posixParseMwdSpec : Parser TransitionSpec := do
  skipChar 'M'

  let month ← parseBoundedNat "month" <* skipChar '.'
  let week ← parseBoundedNat "week" (· ≤ 5) <* skipChar '.'

  -- Convert POSIX day (0=Sunday … 6=Saturday) to ISO ordinal (1=Monday … 7=Sunday).
  let d ← digits
  if d > 6 then fail s!"day {d} out of range 0-6"

  let day ← match (Bounded.LE.ofInt (if d == 0 then 7 else Int.ofNat d)) with
    | some wd => pure wd
    | none => fail s!"day {d} out of range 0-6"

  return .mwd month week day

-- "J" <n> where n is 1–365; Feb 29 is never counted.
private def posixParseJulianSpec : Parser TransitionSpec := do
  skipChar 'J'
  let day : Bounded.LE 1 365 ← parseBoundedNat "Julian day"
  return .julian day

-- <n> where n is 0–365; Feb 29 is counted in leap years.
private def posixParseJulian0Spec : Parser TransitionSpec := do
  let day : Bounded.LE 0 365 ← parseBoundedNat "day"
  return .julian0 day

-- [ <offset> ] — optional DST offset; defaults to stdOffset + 1h when absent.
private def posixParseDstOffset (stdOffset : TimeZone.Offset) : Parser TimeZone.Offset := do
  let c ← peek?
  if let some ch := c then
    if ch.isDigit || ch == '+' || ch == '-' then posixParseOffset
    else pure ⟨Second.Offset.ofInt (stdOffset.second.val + 3600)⟩
  else pure ⟨Second.Offset.ofInt (stdOffset.second.val + 3600)⟩

-- <rule-spec> ::= "M" <month> "." <week> "." <weekday> | "J" <n> | <n>
private def posixParseSpec : Parser TransitionSpec :=
  attempt posixParseMwdSpec <|> attempt posixParseJulianSpec <|> posixParseJulian0Spec

-- <rule> ::= <rule-spec> [ "/" <time> ]
-- When `extended` is true, hours may range from -167 to 167 (TZif v3+).
private def posixParseRule (extended : Bool := false) : Parser TransitionRule := do
  let spec ← posixParseSpec

  -- "The time has the same format as offset except that no leading sign ( '-' or '+' ) is allowed. The default, if time is not given, shall be 02:00:00."
  -- $8.3 https://pubs.opengroup.org/onlinepubs/9699919799/
  let defaultTime : Hour.Offset := 2

  let parseTime := attempt <| do
    skipChar '/'
    let sign ← posixParseSign
    let t ← posixParseHMS (maxHour := if extended then 167 else 24)
    return Second.Offset.ofInt (sign * t.val)

  let time ← parseTime <|> pure defaultTime.toSeconds

  return { spec, time }

-- <TZ> ::= NL <std> <offset> [ <dst> [ <offset> ] [ "," <rule> "," <rule> ] ] NL
private def parsePosixTzP (extended : Bool := false) : Parser RecurringRule := do
  let stdName ← posixParseName

  if stdName.isEmpty then
    fail "empty timezone name"

  let stdOffset ← posixParseOffset

  if (← isEof) then
    return { stdName, stdOffset }

  let dstName ← posixParseName

  if dstName.isEmpty then
    return { stdName, stdOffset }

  let dstOffset ← posixParseDstOffset stdOffset

  if (← peek?) != some ',' then
    return { stdName, stdOffset, dst := some { name := dstName, offset := dstOffset } }

  let startRule ← skip *> posixParseRule extended
  let endRule ← skipChar ',' *> posixParseRule extended

  return {
    stdName,
    stdOffset,
    dst := some {
      name := dstName,
      offset := dstOffset,
      start := some startRule,
      end_ := some endRule
    }
  }

/--
Parse a POSIX TZ footer string into a `RecurringRule`, returning an error on failure.

When `extended` is `true`, transition times accept signed hours in the range
-`167` to `167` instead of the POSIX-required 0 to `24` (TZif version 3+).
-/
def parsePosixTz (s : String) (extended : Bool := false) : Except String RecurringRule :=
  parsePosixTzP extended
  |>.run s

end Std.Time.TimeZone
