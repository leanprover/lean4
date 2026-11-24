/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Util.Reprove
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Elab.Command.reprove]
public def fmtReprove : Fmt := fun
  | `(Lean.Elab.Command.reprove| reprove%$reproveTk $ids:ident* by%$byTk $seq:tacticSeq) => do
    let reproveTk ← fmt reproveTk
    let ids ← fmtArray ids
    let byTk ← fmt byTk
    let seq ← fmt seq
    let ids := Layouts.fill ids
    let signature := Layouts.pseudoApplication #[reproveTk, ids]
    return Layouts.keywordSeparated signature byTk seq
  | _ => throw .partialFormatter
