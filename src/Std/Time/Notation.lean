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
  | .B p => do `(Std.Time.Modifier.B $(← convertText p))
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

def syntaxNat (n : Nat) : MacroM (TSyntax `term) := do
  let info ← MonadRef.mkInfoFromRefPos
  pure { raw := Syntax.node1 info `num (Lean.Syntax.atom info (toString n)) }

def syntaxString (n : String) : MacroM (TSyntax `term) := do
  let info ← MonadRef.mkInfoFromRefPos
  pure { raw := Syntax.node1 info `str (Lean.Syntax.atom info (toString n)) }

def syntaxInt (n : Int) : MacroM (TSyntax `term) := do
  match n with
  | .ofNat n => `(Int.ofNat $(Syntax.mkNumLit <| toString n))
  | .negSucc n => `(Int.negSucc $(Syntax.mkNumLit <| toString n))

def syntaxBounded (n : Int) : MacroM (TSyntax `term) := do
 `(Std.Time.Internal.Bounded.LE.ofNatWrapping $(← syntaxInt n) (by decide))

def syntaxVal (n : Int) : MacroM (TSyntax `term) := do
 `(Std.Time.Internal.UnitVal.ofInt $(← syntaxInt n))

def convertOffset (offset : Std.Time.TimeZone.Offset) : MacroM (TSyntax `term) := do
 `(Std.Time.TimeZone.Offset.mk $(← syntaxVal offset.hour.val) $(← syntaxVal offset.second.val))

def convertTimezone (tz : Std.Time.TimeZone) : MacroM (TSyntax `term) := do
 `(Std.Time.TimeZone.mk $(← convertOffset tz.offset) $(Syntax.mkStrLit tz.name) $(Syntax.mkStrLit tz.abbreviation) false)

def convertPlainDate (d : Std.Time.PlainDate) : MacroM (TSyntax `term) := do
 `(Std.Time.PlainDate.clip $(← syntaxInt d.year) $(← syntaxBounded d.month.val) $(← syntaxBounded d.day.val))

def convertPlainTime (d : Std.Time.PlainTime) : MacroM (TSyntax `term) := do
 `(Std.Time.PlainTime.mk $(← syntaxBounded d.hour.val) $(← syntaxBounded d.minute.val) ⟨true, $(← syntaxBounded d.second.snd.val)⟩ $(← syntaxBounded d.nano.val))

def convertPlainDateTime (d : Std.Time.PlainDateTime) : MacroM (TSyntax `term) := do
 `(Std.Time.PlainDateTime.mk $(← convertPlainDate d.date) $(← convertPlainTime d.time))

def convertZonedDateTime (d : Std.Time.ZonedDateTime) : MacroM (TSyntax `term) := do
 `(Std.Time.ZonedDateTime.mk $(← convertTimezone d.timezone) (DateTime.ofLocalDateTime $(← convertPlainDateTime d.snd.date.get) $(← convertTimezone d.timezone)))

syntax "zoned(" str ")" : term

syntax "datetime(" str ")" : term

syntax "date(" str ")" : term

syntax "time(" str ")" : term

syntax "offset(" str ")" : term

syntax "timezone(" str ")" : term

macro_rules
  | `(zoned( $date:str )) => do
      match ZonedDateTime.fromLeanDateTimeWithZoneString date.getString with
      | .ok res => do
        return ← convertZonedDateTime res
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
