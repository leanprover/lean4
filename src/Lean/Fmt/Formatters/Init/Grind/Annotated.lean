/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Grind.Annotated
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Command.grindAnnotated]
public def fmtGrindAnnotated : Fmt := fun
  | `(Parser.Command.grindAnnotated| grind_annotated%$tk $s:str) => do
    let tk ← fmt tk
    let s ← fmt s
    return Layouts.pseudoApplication #[tk, s]
  | _ => throw .partialFormatter
