/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.Range.Polymorphic.PRange
import Init.Data

namespace Lean.Fmt

public def fmtRange (lhs op rhs : Syntax) : FmtM TaggedDoc := do
  let lhs ← fmt lhs
  let op ← fmt op
  let rhs ← fmt rhs
  return mkSelfDelimited <| Layouts.infixOperator #[lhs, op, rhs] <| .dense (spacing := false)

public def fmtPrefixRange (op rhs : Syntax) : FmtM TaggedDoc := do
  let op ← fmt op
  let rhs ← fmt rhs
  return mkSelfDelimited <| Layouts.prefixOperator op rhs .withoutSpacing

public def fmtPostfixRange (lhs op : Syntax) : FmtM TaggedDoc := do
  let lhs ← fmt lhs
  let op ← fmt op
  return mkSelfDelimited <| Layouts.postfixOperator lhs op .withoutSpacing

@[builtin_fmt Std.«term_..._»]
public def fmtRangeRco : Fmt := fun
  | `($a:term...%$opTk $b:term) => fmtRange a opTk b
  | _ => throw .partialFormatter

@[builtin_fmt Std.«term_...<_»]
public def fmtRangeRcoExcl : Fmt := fun
  | `($a:term...<%$opTk $b:term) => fmtRange a opTk b
  | _ => throw .partialFormatter

@[builtin_fmt Std.«term_...=_»]
public def fmtRangeRcc : Fmt := fun
  | `($a:term...=%$opTk $b:term) => fmtRange a opTk b
  | _ => throw .partialFormatter

@[builtin_fmt Std.«term_<..._»]
public def fmtRangeRoo : Fmt := fun
  | `($a:term<...%$opTk $b:term) => fmtRange a opTk b
  | _ => throw .partialFormatter

@[builtin_fmt Std.«term_<...<_»]
public def fmtRangeRooExcl : Fmt := fun
  | `($a:term<...<%$opTk $b:term) => fmtRange a opTk b
  | _ => throw .partialFormatter

@[builtin_fmt Std.«term_<...=_»]
public def fmtRangeRoc : Fmt := fun
  | `($a:term<...=%$opTk $b:term) => fmtRange a opTk b
  | _ => throw .partialFormatter

@[builtin_fmt Std.«term*..._»]
public def fmtRangeRio : Fmt := fun
  | `(*...%$opTk $b:term) => fmtPrefixRange opTk b
  | _ => throw .partialFormatter

@[builtin_fmt Std.«term*...<_»]
public def fmtRangeRioExcl : Fmt := fun
  | `(*...<%$opTk $b:term) => fmtPrefixRange opTk b
  | _ => throw .partialFormatter

@[builtin_fmt Std.«term*...=_»]
public def fmtRangeRic : Fmt := fun
  | `(*...=%$opTk $b:term) => fmtPrefixRange opTk b
  | _ => throw .partialFormatter

@[builtin_fmt Std.«term_...*»]
public def fmtRangeRci : Fmt := fun
  | `($a:term...*%$opTk) => fmtPostfixRange a opTk
  | _ => throw .partialFormatter

@[builtin_fmt Std.«term_<...*»]
public def fmtRangeRoi : Fmt := fun
  | `($a:term<...*%$opTk) => fmtPostfixRange a opTk
  | _ => throw .partialFormatter
