/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.Range.Basic
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Std.Legacy.Range.«term[:_]»]
public def fmtLegacyRangeUpperBound : Fmt := fun
  | `([%$lbTk :%$colonTk $stop:term]%$rbTk) => do
    let lbTk ← fmt lbTk
    let colonTk ← fmt colonTk
    let stop ← fmt stop
    let rbTk ← fmt rbTk
    let bounds := Layouts.atomic #[colonTk, stop]
    return Layouts.bracketed lbTk bounds rbTk .dense
  | _ => throw .partialFormatter

@[builtin_fmt Std.Legacy.Range.«term[_:_]»]
public def fmtLegacyRangeBounds : Fmt := fun
  | `([%$lbTk $start:term :%$colonTk $stop:term]%$rbTk) => do
    let lbTk ← fmt lbTk
    let start ← fmt start
    let colonTk ← fmt colonTk
    let stop ← fmt stop
    let rbTk ← fmt rbTk
    let bounds := Layouts.infixOperator #[start, colonTk, stop] <| .sparse (spacing := false)
    return Layouts.bracketed lbTk bounds rbTk .dense
  | _ => throw .partialFormatter

@[builtin_fmt Std.Legacy.Range.«term[:_:_]»]
public def fmtLegacyRangeUpperBoundWithStep : Fmt := fun
  | `([%$lbTk :%$lowerColonTk $stop:term :%$upperColonTk $step:term]%$rbTk) => do
    let lbTk ← fmt lbTk
    let lowerColonTk ← fmt lowerColonTk
    let stop ← fmt stop
    let upperColonTk ← fmt upperColonTk
    let step ← fmt step
    let rbTk ← fmt rbTk
    let bounds := Layouts.infixOperator #[stop, upperColonTk, step] <| .sparse (spacing := false)
    let bounds := Layouts.atomic #[lowerColonTk, bounds]
    return Layouts.bracketed lbTk bounds rbTk .dense
  | _ => throw .partialFormatter

@[builtin_fmt Std.Legacy.Range.«term[_:_:_]»]
public def fmtLegacyRangeBoundsWithStep : Fmt := fun
  | `([%$lbTk $start:term :%$lowerColonTk $stop:term :%$upperColonTk $step:term]%$rbTk) => do
    let lbTk ← fmt lbTk
    let start ← fmt start
    let lowerColonTk ← fmt lowerColonTk
    let stop ← fmt stop
    let upperColonTk ← fmt upperColonTk
    let step ← fmt step
    let rbTk ← fmt rbTk
    let bounds :=
      Layouts.infixOperator #[start, lowerColonTk, stop, upperColonTk, step] <|
        .sparse (spacing := false)
    return Layouts.bracketed lbTk bounds rbTk .dense
  | _ => throw .partialFormatter
