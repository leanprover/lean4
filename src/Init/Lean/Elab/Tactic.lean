/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elab.Term
import Init.Lean.Elab.Tactic.Basic

namespace Lean
namespace Elab
namespace Term

@[builtinTermElab tacticBlock] def elabTacticBlock : TermElab :=
fun stx _ =>
  throwError stx ("not implemented yet " ++ stx)

end Term

end Elab
end Lean
