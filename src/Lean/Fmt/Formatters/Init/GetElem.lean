/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.GetElem
import Init.Data

namespace Lean.Fmt

@[builtin_fmt «term__[_]»]
public def fmtGetElem : Fmt := fun
  | `($t:term[%$lbTk $i:term]%$rbTk) => do
    let t ← fmt t
    let lbTk ← fmt lbTk
    let i ← fmt i
    let rbTk ← fmt rbTk
    let idx := Layouts.bracketed lbTk i rbTk .dense
    return mkSelfDelimited <| Layouts.atomic #[t, idx]
  | _ => throw .partialFormatter

@[builtin_fmt «term__[_]_?»]
public def fmtGetElemQuestion : Fmt := fun stx => do
  match stx with
  | `($t:term[%$lbTk $i:term]?) =>
    let rbTk ← getStxArg! stx 4
    let questionTk ← getStxArg! stx 6
    let t ← fmt t
    let lbTk ← fmt lbTk
    let i ← fmt i
    let rbTk ← fmt rbTk
    let questionTk ← fmt questionTk
    let idx := Layouts.bracketed lbTk i rbTk .dense
    return mkSelfDelimited <| Layouts.atomic #[t, idx, questionTk]
  | _ => throw .partialFormatter

@[builtin_fmt «term__[_]_!»]
public def fmtGetElemExclamation : Fmt := fun stx => do
  match stx with
  | `($t:term[%$lbTk $i:term]!) =>
    let rbTk ← getStxArg! stx 4
    let exclamationTk ← getStxArg! stx 6
    let t ← fmt t
    let lbTk ← fmt lbTk
    let i ← fmt i
    let rbTk ← fmt rbTk
    let exclamationTk ← fmt exclamationTk
    let idx := Layouts.bracketed lbTk i rbTk .dense
    return mkSelfDelimited <| Layouts.atomic #[t, idx, exclamationTk]
  | _ => throw .partialFormatter

@[builtin_fmt «term__[_]'_»]
public def fmtGetElemProof : Fmt := fun
  | `($t:term[%$lbTk $i:term]'%$rbTk $h:term) => do
    let t ← fmt t
    let lbTk ← fmt lbTk
    let i ← fmt i
    let rbTk ← fmt rbTk
    let h ← fmt h
    let idx := Layouts.bracketed lbTk i rbTk .dense
    let lhs := Layouts.atomic #[t, idx]
    return nested <| Layouts.atomic #[lhs, h]
  | _ => throw .partialFormatter
