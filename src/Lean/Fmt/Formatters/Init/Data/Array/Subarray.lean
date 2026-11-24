/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.Array.Subarray
import Init.Data

namespace Lean.Fmt

public def fmtSubarraySlice (a lbTk bounds rbTk : TaggedDoc) : TaggedDoc :=
  let slice := Layouts.bracketed lbTk bounds rbTk .dense
  mkSelfDelimited <| Layouts.atomic #[a, slice]

@[builtin_fmt Array.«term__[_:_]»]
public def fmtSubarrayBounds : Fmt := fun
  | `($a:term[%$lbTk $start:term :%$colonTk $stop:term]%$rbTk) => do
    let a ← fmt a
    let lbTk ← fmt lbTk
    let start ← fmt start
    let colonTk ← fmt colonTk
    let stop ← fmt stop
    let rbTk ← fmt rbTk
    let bounds := Layouts.infixOperator #[start, colonTk, stop] <| .sparse (spacing := false)
    return fmtSubarraySlice a lbTk bounds rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Array.«term__[_:]»]
public def fmtSubarrayLowerBound : Fmt := fun
  | `($a:term[%$lbTk $start:term :%$colonTk]%$rbTk) => do
    let a ← fmt a
    let lbTk ← fmt lbTk
    let start ← fmt start
    let colonTk ← fmt colonTk
    let rbTk ← fmt rbTk
    let bounds := Layouts.atomic #[start, colonTk]
    return fmtSubarraySlice a lbTk bounds rbTk
  | _ => throw .partialFormatter

@[builtin_fmt Array.«term__[:_]»]
public def fmtSubarrayUpperBound : Fmt := fun
  | `($a:term[%$lbTk :%$colonTk $stop:term]%$rbTk) => do
    let a ← fmt a
    let lbTk ← fmt lbTk
    let colonTk ← fmt colonTk
    let stop ← fmt stop
    let rbTk ← fmt rbTk
    let bounds := Layouts.atomic #[colonTk, stop]
    return fmtSubarraySlice a lbTk bounds rbTk
  | _ => throw .partialFormatter
