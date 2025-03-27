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
import Std.Time.Format.Basic

namespace Std
namespace Time
open Lean Parser Command Std

private def convertText : Text → MacroM (TSyntax `term)
  | .short => `(Std.Time.Text.short)
  | .full => `(Std.Time.Text.full)
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

/--
Syntax for defining a date spec at compile time.
-/
syntax "datespec(" str ")" : term

/--
Syntax for defining a date spec and configuration of this date spec at compile time.
-/
syntax "datespec(" str "," term ")" : term

def formatStringToFormat (fmt : TSyntax `str) (config : Option (TSyntax `term)) : MacroM (TSyntax `term) := do
  let input := fmt.getString
  let format : Except String (GenericFormat .any) := GenericFormat.spec input
  match format with
  | .ok res =>
    let alts ← res.string.mapM convertFormatPart
    let alts := alts.foldl Syntax.TSepArray.push (Syntax.TSepArray.mk #[] (sep := ","))
    let config := config.getD (← `({}))
    `(⟨$config, [$alts,*]⟩)
  | .error err =>
    Macro.throwErrorAt fmt s!"cannot compile spec: {err}"

macro_rules
  | `(datespec( $fmt:str )) => formatStringToFormat fmt none
  | `(datespec( $fmt:str, $config:term )) => formatStringToFormat fmt config
