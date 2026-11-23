/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Std.Time.Notation.Spec
meta import Std.Time.Notation
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Std.Time.«termZoned(_)»]
public def fmtZonedDateTime : Fmt := fun
  | `(zoned(%$lbTk $spec:str )%$rbTk) => do
    let lbTk ← fmt lbTk
    let spec ← fmt spec
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[spec]] rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Std.Time.«termZoned(_,_)»]
public def fmtZonedDateTimeWithTimeZone : Fmt := fun
  | `(zoned(%$lbTk $spec:str ,%$commaTk $timeZone:term )%$rbTk) => do
    let lbTk ← fmt lbTk
    let spec ← fmt spec
    let commaTk ← fmt commaTk
    let timeZone ← fmt timeZone
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[spec], .sep commaTk, .elems #[timeZone]] rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Std.Time.«termDatetime(_)»]
public def fmtPlainDateTime : Fmt := fun
  | `(datetime(%$lbTk $spec:str )%$rbTk) => do
    let lbTk ← fmt lbTk
    let spec ← fmt spec
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[spec]] rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Std.Time.«termDate(_)»]
public def fmtPlainDate : Fmt := fun
  | `(date(%$lbTk $spec:str )%$rbTk) => do
    let lbTk ← fmt lbTk
    let spec ← fmt spec
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[spec]] rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Std.Time.«termTime(_)»]
public def fmtPlainTime : Fmt := fun
  | `(time(%$lbTk $spec:str )%$rbTk) => do
    let lbTk ← fmt lbTk
    let spec ← fmt spec
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[spec]] rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Std.Time.«termOffset(_)»]
public def fmtTimeZoneOffset : Fmt := fun
  | `(offset(%$lbTk $spec:str )%$rbTk) => do
    let lbTk ← fmt lbTk
    let spec ← fmt spec
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[spec]] rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Std.Time.«termTimezone(_)»]
public def fmtTimeZone : Fmt := fun
  | `(timezone(%$lbTk $spec:str )%$rbTk) => do
    let lbTk ← fmt lbTk
    let spec ← fmt spec
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk #[.elems #[spec]] rbTk
  | _ => throw .partialFormatter
