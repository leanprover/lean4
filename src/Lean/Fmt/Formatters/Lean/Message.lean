/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Message
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.termM!_]
public def fmtMessageDataInterpolation : Fmt := fun
  | `(m!%$mTk $s:interpolatedStr) => do
    let mTk ← fmt mTk
    let s ← fmt s
    return Layouts.strLit mTk s
  | _ => throw .partialFormatter
