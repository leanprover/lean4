/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.ByCases
import Init.Data

namespace Lean.Fmt

@[builtin_fmt «tacticBy_cases_:_»]
public def fmtByCases : Fmt := fun
  | `(tactic| by_cases%$byCasesTk $[$h?:ident :%$colonTk?]? $e:term) => do
    let byCasesTk ← fmt byCasesTk
    let h? ← fmt? h?
    let colonTk? ← fmt? colonTk?
    let e ← fmt e
    let hypothesis := Layouts.typeAscription h? colonTk? e
    return Layouts.pseudoApplication #[byCasesTk, hypothesis]
  | _ => throw .partialFormatter
