/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elab.Tactic.Basic

namespace Lean
namespace Elab
namespace Tactic

@[builtinTactic «induction»] def evalInduction : Tactic :=
fun stx => focus stx $
  throwError stx ("WIP " ++ stx)

end Tactic
end Elab
end Lean
