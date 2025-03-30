/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Date
import Std.Time.Time
import Std.Time.Zoned
import Std.Time.DateTime
import Std.Time.Format

namespace Std
namespace Time
open Lean Parser Command Std

set_option linter.all true

private def convertText : Text → MacroM (TSyntax `term)
  | .short  => `(Std.Time.Text.short)
  | .full   => `(Std.Time.Text.full)
  | .narrow => `(Std.Time.Text.narrow)

private def convertNumber : Number → MacroM (TSyntax `term)
  | ⟨padding⟩ => `(Std.Time.Number.mk $(quote padding))

private def convertFraction : Fraction → MacroM (TSyntax `term)
  | .nano => `(Std.Time.Fraction.nano)
  | .truncated digits => `(Std.Time.Fraction.truncated $(quote digits))

private def convertYear : Year → MacroM (TSyntax `term)
  | .any => `(Std.Time.Year.any)
  | .twoDigit => `(Std.Time.Year.twoDigit)
  | .fourDigit => `(Std.Time.Year.fourDigit)
  | .extended n => `(Std.Time.Year.extended $(quote n))

private def convertZoneName : ZoneName → MacroM (TSyntax `term)
  | .short => `(Std.Time.ZoneName.short)
  | .full => `(Std.Time.ZoneName.full)

private def convertOffsetX : OffsetX → MacroM (TSyntax `term)
  | .hour => `(Std.Time.OffsetX.hour)
  | .hourMinute => `(Std.Time.OffsetX.hourMinute)
  | .hourMinuteColon => `(Std.Time.OffsetX.hourMinuteColon)
  | .hourMinuteSecond => `(Std.Time.OffsetX.hourMinuteSecond)
  | .hourMinuteSecondColon => `(Std.Time.OffsetX.hourMinuteSecondColon)

private def convertOffsetO : OffsetO → MacroM (TSyntax `term)
  | .short => `(Std.Time.OffsetO.short)
  | .full  => `(Std.Time.OffsetO.full)

private def convertOffsetZ : OffsetZ → MacroM (TSyntax `term)
  | .hourMinute => `(Std.Time.OffsetZ.hourMinute)
  | .full => `(Std.Time.OffsetZ.full)
  | .hourMinuteSecondColon => `(Std.Time.OffsetZ.hourMinuteSecondColon)

private def convertModifier : Modifier → MacroM (TSyntax `term)
  | .G p => do `(Std.Time.Modifier.G $(← convertText p))
  | .y p => do `(Std.Time.Modifier.y $(← convertYear p))
  | .u p => do `(Std.Time.Modifier.u $(← convertYear p))
  | .D p => do `(Std.Time.Modifier.D $(← convertNumber p))
  | .MorL p =>
    match p with
    | .inl num => do `(Std.Time.Modifier.MorL (.inl $(← convertNumber num)))
    | .inr txt => do `(Std.Time.Modifier.MorL (.inr $(← convertText txt)))
  | .d p => do `(Std.Time.Modifier.d $(← convertNumber p))
  | .Qorq p =>
    match p with
    | .inl num => do `(Std.Time.Modifier.Qorq (.inl $(← convertNumber num)))
    | .inr txt => do `(Std.Time.Modifier.Qorq (.inr $(← convertText txt)))
  | .w p => do `(Std.Time.Modifier.w $(← convertNumber p))
  | .W p => do `(Std.Time.Modifier.W $(← convertNumber p))
  | .E p => do `(Std.Time.Modifier.E $(← convertText p))
  | .eorc p =>
    match p with
    | .inl num => do `(Std.Time.Modifier.eorc (.inl $(← convertNumber num)))
    | .inr txt => do `(Std.Time.Modifier.eorc (.inr $(← convertText txt)))
  | .F p => do `(Std.Time.Modifier.F $(← convertNumber p))
  | .a p => do `(Std.Time.Modifier.a $(← convertText p))
  | .h p => do `(Std.Time.Modifier.h $(← convertNumber p))
  | .K p => do `(Std.Time.Modifier.K $(← convertNumber p))
  | .k p => do `(Std.Time.Modifier.k $(← convertNumber p))
  | .H p => do `(Std.Time.Modifier.H $(← convertNumber p))
  | .m p => do `(Std.Time.Modifier.m $(← convertNumber p))
  | .s p => do `(Std.Time.Modifier.s $(← convertNumber p))
  | .S p => do `(Std.Time.Modifier.S $(← convertFraction p))
  | .A p => do `(Std.Time.Modifier.A $(← convertNumber p))
  | .n p => do `(Std.Time.Modifier.n $(← convertNumber p))
  | .N p => do `(Std.Time.Modifier.N $(← convertNumber p))
  | .V => `(Std.Time.Modifier.V)
  | .z p => do `(Std.Time.Modifier.z $(← convertZoneName p))
  | .O p => do `(Std.Time.Modifier.O $(← convertOffsetO p))
  | .X p => do `(Std.Time.Modifier.X $(← convertOffsetX p))
  | .x p => do `(Std.Time.Modifier.x $(← convertOffsetX p))
  | .Z p => do `(Std.Time.Modifier.Z $(← convertOffsetZ p))

private def convertFormatPart : FormatPart → MacroM (TSyntax `term)
  | .string s => `(.string $(Syntax.mkStrLit s))
  | .modifier mod => do `(.modifier $(← convertModifier mod))

private def syntaxNat (n : Nat) : MacroM (TSyntax `term) := do
  let info ← MonadRef.mkInfoFromRefPos
  pure { raw := Syntax.node1 info `num (Lean.Syntax.atom info (toString n)) }

private def syntaxString (n : String) : MacroM (TSyntax `term) := do
  let info ← MonadRef.mkInfoFromRefPos
  pure { raw := Syntax.node1 info `str (Lean.Syntax.atom info (toString n)) }

private def syntaxInt (n : Int) : MacroM (TSyntax `term) := do
  match n with
  | .ofNat n => `(Int.ofNat $(Syntax.mkNumLit <| toString n))
  | .negSucc n => `(Int.negSucc $(Syntax.mkNumLit <| toString n))

private def syntaxBounded (n : Int) : MacroM (TSyntax `term) := do
 `(Std.Time.Internal.Bounded.LE.ofNatWrapping $(← syntaxInt n) (by decide))

private def syntaxVal (n : Int) : MacroM (TSyntax `term) := do
 `(Std.Time.Internal.UnitVal.ofInt $(← syntaxInt n))

private def convertOffset (offset : Std.Time.TimeZone.Offset) : MacroM (TSyntax `term) := do
 `(Std.Time.TimeZone.Offset.ofSeconds $(← syntaxVal offset.second.val))

private def convertTimezone (tz : Std.Time.TimeZone) : MacroM (TSyntax `term) := do
 `(Std.Time.TimeZone.mk $(← convertOffset tz.offset) $(Syntax.mkStrLit tz.name) $(Syntax.mkStrLit tz.abbreviation) false)

private def convertPlainDate (d : Std.Time.PlainDate) : MacroM (TSyntax `term) := do
 `(Std.Time.PlainDate.ofYearMonthDayClip $(← syntaxInt d.year) $(← syntaxBounded d.month.val) $(← syntaxBounded d.day.val))

private def convertPlainTime (d : Std.Time.PlainTime) : MacroM (TSyntax `term) := do
 `(Std.Time.PlainTime.mk $(← syntaxBounded d.hour.val) $(← syntaxBounded d.minute.val) $(← syntaxBounded d.second.val) $(← syntaxBounded d.nanosecond.val))

private def convertPlainDateTime (d : Std.Time.PlainDateTime) : MacroM (TSyntax `term) := do
 `(Std.Time.PlainDateTime.mk $(← convertPlainDate d.date) $(← convertPlainTime d.time))

private def convertZonedDateTime (d : Std.Time.ZonedDateTime) (identifier := false) : MacroM (TSyntax `term) := do
  let plain ← convertPlainDateTime d.toPlainDateTime

  if identifier then
    `(Std.Time.ZonedDateTime.ofPlainDateTime $plain <$> Std.Time.Database.defaultGetZoneRules $(Syntax.mkStrLit d.timezone.name))
  else
    `(Std.Time.ZonedDateTime.ofPlainDateTime $plain (Std.Time.TimeZone.ZoneRules.ofTimeZone $(← convertTimezone d.timezone)))

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
      match ZonedDateTime.fromLeanDateTimeWithZoneString date.getString with
      | .ok res => do return ← convertZonedDateTime res
      | .error _ =>
        match ZonedDateTime.fromLeanDateTimeWithIdentifierString date.getString with
        | .ok res => do return ← convertZonedDateTime res (identifier := true)
        | .error res => Macro.throwErrorAt date s!"error: {res}"

  | `(zoned( $date:str, $timezone )) => do
      match PlainDateTime.fromLeanDateTimeString date.getString with
      | .ok res => do
        let plain ← convertPlainDateTime res
        `(Std.Time.ZonedDateTime.ofPlainDateTime $plain $timezone)
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
