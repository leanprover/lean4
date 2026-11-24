/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Elab.Quotation
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Elab.Term.Quotation.commandElab_stx_quot_]
public def fmtElabStxQuot : Fmt := fun
  | `(command| elab_stx_quot%$elabStxQuotTk $kind:ident) => do
    let elabStxQuotTk ← fmt elabStxQuotTk
    let kind ← fmt kind
    return Layouts.pseudoApplication #[elabStxQuotTk, kind]
  | _ => throw .partialFormatter
