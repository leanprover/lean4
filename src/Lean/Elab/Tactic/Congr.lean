/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Congr
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Tactic

namespace Lean.Elab.Tactic
@[builtin_tactic Parser.Tactic.congr] def evalCongr : Tactic := fun stx =>
  match stx with
  | `(tactic| congr $[$n?]?) =>
    let hugeDepth := 1000000
    let depth := n?.map (·.getNat) |>.getD hugeDepth
    liftMetaTactic fun mvarId => mvarId.congrN depth
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic


