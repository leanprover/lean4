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
import Lean.Elab.Command

namespace Std
namespace Time
open Lean.Elab Term Lean Parser Command Std

/--
Category of units that are valid inside a date.
-/
declare_syntax_cat date_component

/--
Raw numbers
-/
syntax num : date_component

/--
Strings for dates like `"1970"-"1"-"1"`
-/
syntax str : date_component

/--
Variables inside of the date.
-/
syntax ident : date_component

private def parseComponent : TSyntax `date_component -> MacroM (TSyntax `term)
  | `(date_component| $num:num) => `($num)
  | `(date_component| $str:str) => `($(Syntax.mkNumLit str.getString))
  | `(date_component| $ident:ident) => `($ident:ident)
  | syn => Macro.throwErrorAt syn "unsupported syntax"

/--
Category of dates like `DD-MM-YYYY`.
-/
declare_syntax_cat date

/--
Date in `DD-MM-YYYY` format.
-/
syntax date_component noWs "-" noWs date_component noWs "-" noWs date_component : date

private def parseDate : TSyntax `date -> MacroM (TSyntax `term)
  | `(date|$day:date_component-$month:date_component-$year:date_component) => do
    `(Std.Time.LocalDate.mk $(← parseComponent year) $(← parseComponent month) $(← parseComponent day) (by decide))
  | syn => Macro.throwErrorAt syn "unsupported type"

/--
Category of times like `HH:mm:ss`.
-/
declare_syntax_cat time

/--
Date in `HH-mm-ss` format.
-/
syntax date_component noWs ":" noWs date_component noWs ":" noWs date_component : time

/--
Date in `HH-mm-ss.sssssss` format.
-/
syntax date_component noWs ":" noWs date_component noWs ":" noWs date_component "." noWs date_component : time

private def parseTime : TSyntax `time -> MacroM (TSyntax `term)
  | `(time| $hour:date_component:$minute:date_component:$second:date_component) => do
    `(Std.Time.LocalTime.mk $(← parseComponent hour) $(← parseComponent minute) $(← parseComponent second) 0)
  | `(time| $hour:date_component:$minute:date_component:$second:date_component.$nanos:date_component) => do
    `(Std.Time.LocalTime.mk $(← parseComponent hour) $(← parseComponent minute) $(← parseComponent second) $(← parseComponent nanos))
  | syn => Macro.throwErrorAt syn "unsupported syntax"

/--
Category of date and time together.
-/
declare_syntax_cat datetime

/--
Date and time in `YYYY-MM-DD:HH:mm:ss` format.
-/
syntax date noWs ":" noWs time : datetime

/--
Date but using timestamp.
-/
syntax date_component : datetime

private def parseDateTime : TSyntax `datetime -> MacroM (TSyntax `term)
  | `(datetime| $date:date:$time:time) => do
    `(Std.Time.LocalDateTime.mk $(← parseDate date)  $(← parseTime time))
  | `(datetime|$tm:date_component) => do
    `(Std.Time.LocalDateTime.ofTimestamp $(← parseComponent tm))
  | syn => Macro.throwErrorAt syn "unsupported syntax"

/--
Category of offsets like `+00:00`.
-/
declare_syntax_cat offset

/--
Timezone in `+HH:mm`, or `-HH:mm` format.
-/
syntax ("+" <|> "-") date_component ":" date_component : offset

private def parseOffset : TSyntax `offset -> MacroM (TSyntax `term)
  | `(offset| +$hour:date_component:$minutes:date_component) => do
    `(Std.Time.TimeZone.Offset.ofHoursAndMinutes $(← parseComponent hour) $(← parseComponent minutes))
  | `(offset| -$hour:date_component:$minutes:date_component) => do
    `(Std.Time.TimeZone.Offset.ofHoursAndMinutes (- $(← parseComponent hour)) (-$(← parseComponent minutes)))
  | syn => Macro.throwErrorAt syn "unsupported syntax"

/--
Category of timezones like `Z`, `UTC`, `GMT` and `+HH:mm`.
-/
declare_syntax_cat zone

/--
Timezone in `+HHmm`, or `-HHmm` format.
-/
syntax (offset <|> "UTC" <|> "GMT" <|> "Z" <|> ("(" term ")")) : zone

private def parseZone : TSyntax `zone -> MacroM (TSyntax `term)
  | `(zone| ($term)) => do `($term)
  | `(zone| UTC) => do `(Std.Time.TimeZone.UTC)
  | `(zone| GMT) => do `(Std.Time.TimeZone.GMT)
  | `(zone| Z) => do `(Std.Time.TimeZone.UTC)
  | `(zone| $offset:offset) => do `(Std.Time.TimeZone.mk $(← parseOffset offset) "Offset")
  | syn => Macro.throwErrorAt syn "unsupported syntax"

/--
Datetimes with zone.
-/
declare_syntax_cat zoned

/--
Datetime with zone in `YYYY-MM-DDTHH:mm:ssZ` format.
-/
syntax datetime zone : zoned

private def parseZoned : TSyntax `zoned -> MacroM (TSyntax `term)
  | `(zoned| $timestamp:num $zone) => do
    `(Std.Time.DateTime.ofTimestamp $timestamp $(← parseZone zone))
  | `(zoned| $datetime:datetime $zone) => do
    `(Std.Time.DateTime.ofLocalDateTime $(← parseDateTime datetime) $(← parseZone zone))
  | syn => Macro.throwErrorAt syn "unsupported syntax"

/--
Syntax for zones.
-/
syntax "zone%" zone : term

/--
Zoned date times.
-/
syntax "date%" zoned : term

/--
Normal datetimes.
-/
syntax "date%" datetime : term

/--
Macro for defining dates.
-/
syntax (name := dateDate) "date%" date : term

/--
Macro for defining times.
-/
syntax "date%" time : term

/--
Macro for creating offsets
-/
syntax "offset%" offset : term

/--
Macro for creating timezones
-/
syntax "timezone%" ident noWs "/" noWs ident offset : term

/--
Macro for creating timezones with string
-/
syntax "timezone%" str offset : term

macro_rules
  | `(date% $date:date) => parseDate date
  | `(date% $time:time) => parseTime time
  | `(date% $datetime:datetime) => parseDateTime datetime
  | `(date% $zoned:zoned) => parseZoned zoned
  | `(offset% $offset:offset) => parseOffset offset
  | `(timezone% $str $offset:offset) => do
    do `(Std.Time.TimeZone.mk $(← parseOffset offset) $str)
  | `(timezone% $name/$sub $offset:offset) => do
    let name := s!"{name.getId.toString}/{sub.getId.toString}"
    let syn := Syntax.mkStrLit name
    do `(Std.Time.TimeZone.mk $(← parseOffset offset) $syn)

private def convertModifier : Modifier → MacroM (TSyntax `term)
  | .YYYY => `(Std.Time.Modifier.YYYY)
  | .YY => `(Std.Time.Modifier.YY)
  | .MMMM => `(Std.Time.Modifier.MMMM)
  | .MMM => `(Std.Time.Modifier.MMM)
  | .MM => `(Std.Time.Modifier.MM)
  | .M => `(Std.Time.Modifier.M)
  | .DD => `(Std.Time.Modifier.DD)
  | .D => `(Std.Time.Modifier.D)
  | .d => `(Std.Time.Modifier.d)
  | .EEEE => `(Std.Time.Modifier.EEEE)
  | .EEE => `(Std.Time.Modifier.EEE)
  | .hh => `(Std.Time.Modifier.hh)
  | .h => `(Std.Time.Modifier.h)
  | .HH => `(Std.Time.Modifier.HH)
  | .H => `(Std.Time.Modifier.H)
  | .AA => `(Std.Time.Modifier.AA)
  | .aa => `(Std.Time.Modifier.aa)
  | .mm => `(Std.Time.Modifier.mm)
  | .m => `(Std.Time.Modifier.m)
  | .sss => `(Std.Time.Modifier.sss)
  | .ss => `(Std.Time.Modifier.ss)
  | .s => `(Std.Time.Modifier.s)
  | .ZZZZZ => `(Std.Time.Modifier.ZZZZZ)
  | .ZZZZ => `(Std.Time.Modifier.ZZZZ)
  | .ZZZ => `(Std.Time.Modifier.ZZZ)
  | .Z => `(Std.Time.Modifier.Z)
  | .z => `(Std.Time.Modifier.z)

private def convertFormatPart : FormatPart → MacroM (TSyntax `term)
  | .string s => `(.string $(Syntax.mkStrLit s))
  | .modifier mod => do `(.modifier $(← convertModifier mod))

/--
Syntax for defining a date spec at compile time.
-/
syntax "date-spec%" str : term

macro_rules
  | `(date-spec% $format_string) => do
    let input := format_string.getString
    let format : Except String (Format .any) := Format.spec input
    match format with
    | .ok res =>
      let alts ← res.string.mapM convertFormatPart
      let alts := alts.foldl Syntax.TSepArray.push (Syntax.TSepArray.mk #[] (sep := ","))
      `(⟨[$alts,*]⟩)
    | .error err =>
      Macro.throwErrorAt format_string s!"cannot compile spec: {err}"
