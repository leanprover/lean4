/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Exception
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.termThrowError__]
public def fmtThrowError : Fmt := fun
  | `(termThrowError__| throwError%$throwErrorTk $msg:term) => do fmtAppLike #[throwErrorTk, msg]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.termThrowErrorAt____]
public def fmtThrowErrorAt : Fmt := fun
  | `(termThrowErrorAt____| throwErrorAt%$throwErrorAtTk $ref:term $msg:term) => do
    fmtAppLike #[throwErrorAtTk, ref, msg]
  | _ =>
    throw .partialFormatter
