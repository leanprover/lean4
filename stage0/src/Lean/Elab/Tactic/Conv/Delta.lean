/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.Delta
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

@[builtinTactic Lean.Parser.Tactic.Conv.delta] def evalDelta : Tactic := fun stx => withMainContext do
  let declName ← resolveGlobalConstNoOverload stx[1]
  let lhsNew ← deltaExpand (← getLhs) (. == declName)
  changeLhs lhsNew

end Lean.Elab.Tactic.Conv
