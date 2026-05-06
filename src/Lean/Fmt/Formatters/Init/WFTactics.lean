/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.WFTactics
import Init.Data

namespace Lean.Fmt

@[builtin_fmt tacticDecreasing_with_]
public def fmtDecreasingWith : Fmt := fun
  | `(tactic| decreasing_with%$decreasingWithTk $ts:tacticSeq) => do
    let decreasingWithTk ← fmt decreasingWithTk
    let ts ← fmt ts
    return Layouts.keywordPrefixedSeq decreasingWithTk ts .nonSticky
  | _ => throw .partialFormatter
