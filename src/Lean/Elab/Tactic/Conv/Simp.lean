/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

@[builtinTactic Lean.Parser.Tactic.Conv.simp] def evalSimp : Tactic := fun stx => do
  let { ctx, .. } ← mkSimpContext stx (eraseLocal := false)
  let lhs ← getLhs
  let result ← simp lhs ctx
  if result.proof?.isNone then
    changeLhs result.expr
  else
    updateLhs result.expr (← result.getProof)

end Lean.Elab.Tactic.Conv
