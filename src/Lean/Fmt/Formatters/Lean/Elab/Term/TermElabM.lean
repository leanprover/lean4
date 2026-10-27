/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Elab.Term.TermElabM
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Term.elabToSyntax]
public def fmtElabToSyntax : Fmt := fun stx => do
  -- `elabToSyntax%` is itself a token, so `elabToSyntax%$tk` would not bind the keyword.
  let `(Parser.Term.elabToSyntax| elabToSyntax% $idx:num) := stx
    | throw .partialFormatter
  fmtAppLike #[← getStxArg! stx 0, idx]
