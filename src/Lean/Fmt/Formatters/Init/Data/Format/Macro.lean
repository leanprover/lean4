/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.Format.Macro
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Std.«termF!_»]
public def fmtFormatInterpolation : Fmt := fun
  | `(f!%$fTk $s:interpolatedStr) => do
    let fTk ← fmt fTk
    let s ← fmt s
    return Layouts.strLit fTk s
  | _ => throw .partialFormatter
