/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term

/-
Auxiliary elaboration functions: AKA custom elaborators
-/

namespace Lean.Elab.Term

@[builtinTermElab forInMacro] def elabForIn : TermElab :=  fun stx expectedType? => do
  match stx with
  | `(forIn! $c $e $body) => elabTerm (← `(forIn $c $e $body)) expectedType?
  | _ => throwUnsupportedSyntax

end Lean.Elab.Term
