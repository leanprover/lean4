/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Data.Html.Elab
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Elab.Html.htmlCmd]
public def fmtHtmlCmd : Fmt := fun
  | `(command| #html%$htmlTk $t:term) => do
    let htmlTk ← fmt htmlTk
    let t ← fmt t
    return Layouts.pseudoApplication #[htmlTk, t]
  | _ => throw .partialFormatter
