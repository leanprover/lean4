/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Format
public meta import Std.Time.Format
meta import Init.Data.String.TakeDrop

public section

namespace Std
namespace Time
open Lean Parser Command Std

set_option linter.all true

private meta def syntaxNat (n : Nat) : MacroM (TSyntax `term) := do
  let info ← MonadRef.mkInfoFromRefPos
  pure { raw := Syntax.node1 info `num (Lean.Syntax.atom info (toString n)) }

private meta def syntaxString (n : String) : MacroM (TSyntax `term) := do
  let info ← MonadRef.mkInfoFromRefPos
  pure { raw := Syntax.node1 info `str (Lean.Syntax.atom info (toString n)) }

private meta def syntaxInt (n : Int) : MacroM (TSyntax `term) := do
  match n with
  | .ofNat n => `(Int.ofNat $(Syntax.mkNumLit <| toString n))
  | .negSucc n => `(Int.negSucc $(Syntax.mkNumLit <| toString n))

private meta def syntaxBounded (n : Int) : MacroM (TSyntax `term) := do
 `(Std.Time.Internal.Bounded.LE.ofNatWrapping $(← syntaxInt n) (by decide))

private meta def syntaxVal (n : Int) : MacroM (TSyntax `term) := do
 `(Std.Time.Internal.UnitVal.ofInt $(← syntaxInt n))

private meta def convertOffset (offset : Std.Time.TimeZone.Offset) : MacroM (TSyntax `term) := do
 `(Std.Time.TimeZone.Offset.ofSeconds $(← syntaxVal offset.second.val))

private meta def convertTimezone (tz : Std.Time.TimeZone) : MacroM (TSyntax `term) := do
 `(Std.Time.TimeZone.mk $(← convertOffset tz.offset) $(Syntax.mkStrLit tz.name) $(Syntax.mkStrLit tz.abbreviation) false)

private meta def convertPlainDate (d : Std.Time.PlainDate) : MacroM (TSyntax `term) := do
 `(Std.Time.PlainDate.ofYearMonthDayClip $(← syntaxInt d.year) $(← syntaxBounded d.month.val) $(← syntaxBounded d.day.val))

private meta def convertPlainTime (d : Std.Time.PlainTime) : MacroM (TSyntax `term) := do
 `(Std.Time.PlainTime.mk $(← syntaxBounded d.hour.val) $(← syntaxBounded d.minute.val) $(← syntaxBounded d.second.val) $(← syntaxBounded d.nanosecond.val))

private meta def convertPlainDateTime (d : Std.Time.PlainDateTime) : MacroM (TSyntax `term) := do
 `(Std.Time.PlainDateTime.mk $(← convertPlainDate d.date) $(← convertPlainTime d.time))

private meta def convertDateTime (d : Std.Time.DateTime) (identifier := false) : MacroM (TSyntax `term) := do
  let plain ← convertPlainDateTime d.toPlainDateTime

  if identifier then
    `(Std.Time.DateTime.ofPlainDateTime $plain <$> Std.Time.Database.defaultGetZoneRules $(Syntax.mkStrLit d.timezone.name))
  else
    `(Std.Time.DateTime.ofPlainDateTime $plain (Std.Time.TimeZone.ZoneRules.ofTimeZone $(← convertTimezone d.timezone)))

/--
Whether a bracketed zone id names a fixed zone rather than a database entry: an offset such as
`+01:00` or `GMT+01:00`, or `TimeZone.GMT`'s name.
-/
private meta def isFixedZoneId (name : String) : Bool :=
  let offset := if name.startsWith "GMT" then (name.drop 3).copy else name
  name == TimeZone.GMT.name || (TimeZone.Offset.fromOffset offset).isOk

/--
Defines a syntax for zoned datetime values. It expects a string representing a datetime with
timezone information.

Example:
`zoned("2024-10-13T15:00:00-03:00")`
-/
syntax "zoned(" str ")" : term

/--
Defines a syntax for zoned datetime values. It expects a string representing a datetime and a
timezone information as a term.

Example:
`zoned("2024-10-13T15:00:00", timezone)`
-/
syntax "zoned(" str "," term ")" : term

/--
Defines a syntax for datetime values without timezone. The input should be a string in an
ISO8601-like format.

Example:
`datetime("2024-10-13T15:00:00")`
-/
syntax "datetime(" str ")" : term

/--
Defines a syntax for date-only values. The input string represents a date in formats like "YYYY-MM-DD".

Example:
`date("2024-10-13")`
-/
syntax "date(" str ")" : term

/--
Defines a syntax for time-only values. The string should represent a time, either in 24-hour or
12-hour format.

Example:
`time("15:00:00")` or `time("03:00:00 PM")`
-/
syntax "time(" str ")" : term

/--
Defines a syntax for UTC offset values. The string should indicate the time difference from UTC
(e.g., "-03:00").

Example:
`offset("-03:00")`
-/
syntax "offset(" str ")" : term

/--
Defines a syntax for timezone identifiers. The input string should be a valid timezone name or
abbreviation.

Example:
`timezone("America/Sao_Paulo")`
-/
syntax "timezone(" str ")" : term

macro_rules
  | `(zoned( $date:str )) => do
      match DateTime.fromLeanDateTimeWithZoneString date.getString with
      | .ok res => do return ← convertDateTime res
      | .error _ =>
        match DateTime.fromLeanDateTimeWithIdentifierString date.getString with
        | .ok res => do return ← convertDateTime res (identifier := !isFixedZoneId res.timezone.name)
        | .error res => Macro.throwErrorAt date s!"error: {res}"

  | `(zoned( $date:str, $timezone )) => do
      match PlainDateTime.fromLeanDateTimeString date.getString with
      | .ok res => do
        let plain ← convertPlainDateTime res
        `(Std.Time.DateTime.ofPlainDateTime $plain $timezone)
      | .error res => Macro.throwErrorAt date s!"error: {res}"

  | `(datetime( $date:str )) => do
      match PlainDateTime.fromLeanDateTimeString date.getString with
      | .ok res => do
        return ← convertPlainDateTime res
      | .error res => Macro.throwErrorAt date s!"error: {res}"

  | `(date( $date:str )) => do
      match PlainDate.fromSQLDateString date.getString with
      | .ok res => return ← convertPlainDate res
      | .error res => Macro.throwErrorAt date s!"error: {res}"

  | `(time( $time:str )) => do
      match PlainTime.fromLeanTime24Hour time.getString with
      | .ok res => return ← convertPlainTime res
      | .error res => Macro.throwErrorAt time s!"error: {res}"

  | `(offset( $offset:str )) => do
      match TimeZone.Offset.fromOffset offset.getString with
      | .ok res => return ← convertOffset res
      | .error res => Macro.throwErrorAt offset s!"error: {res}"

  | `(timezone( $tz:str )) => do
      match TimeZone.fromTimeZone tz.getString with
      | .ok res => return ← convertTimezone res
      | .error res => Macro.throwErrorAt tz s!"error: {res}"
