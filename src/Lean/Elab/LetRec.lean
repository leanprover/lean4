/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Attributes
import Lean.Elab.Binders

namespace Lean
namespace Elab
namespace Term

@[builtinTermElab «letrec»] def elabLetRec : TermElab :=
fun stx expectedType? =>
  throwError ("WIP " ++ stx)

end Term
end Elab
end Lean
