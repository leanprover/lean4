/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.Unfold
import Lean.Elab.Tactic.Conv.Simp

namespace Lean.Elab.Tactic.Conv
open Meta

@[builtinTactic Lean.Parser.Tactic.Conv.unfold] def evalUnfold : Tactic := fun stx => withMainContext do
  let declName ← resolveGlobalConstNoOverload stx[1]
  applySimpResult (← unfold (← getLhs) declName)

end Lean.Elab.Tactic.Conv
