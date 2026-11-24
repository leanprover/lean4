/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Data.ToString.Macro
import Init.Data

namespace Lean.Fmt

@[builtin_fmt «termS!_»]
public def fmtStringInterpolation : Fmt := fun
  | `(s!%$sTk $s:interpolatedStr) => do
    let sTk ← fmt sTk
    let s ← fmt s
    return Layouts.strLit sTk s
  | _ => throw .partialFormatter
