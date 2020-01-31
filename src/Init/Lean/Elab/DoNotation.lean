/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Term
import Init.Lean.Elab.Quotation

namespace Lean
namespace Elab
namespace Term

@[builtinTermElab «do»] def elabDo : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
-- TODO: implement more than the bare minimum necessary for the paper example
| `(do $x:ident ← $e:term; $f:term) => `(HasBind.bind $e (fun $x:ident => $f:term))
| _                                 => throwUnsupportedSyntax

end Term
end Elab
end Lean
