/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectFVars
import Lean.Elab.Term

namespace Lean.Elab.Term
open Meta

def collectUsedFVars (e : Expr) : StateRefT CollectFVars.State MetaM Unit := do
  let e ← instantiateMVars e
  modify fun used => collectFVars used e

def collectUsedFVarsAtFVars (fvars : Array Expr) : StateRefT CollectFVars.State MetaM Unit :=
  fvars.forM fun fvar => do
    let fvarType ← inferType fvar
    collectUsedFVars fvarType

def removeUnused (vars : Array Expr) (used : CollectFVars.State) : MetaM (LocalContext × LocalInstances × Array Expr) := do
  let localInsts ← getLocalInstances
  let lctx ← getLCtx
  let (lctx, localInsts, newVars, _) ← vars.foldrM
    (fun var (result : LocalContext × LocalInstances × Array Expr × CollectFVars.State) => do
      let (lctx, localInsts, newVars, used) := result
      if used.fvarSet.contains var.fvarId! then
        let varType ← inferType var
        let (_, used) ← (collectUsedFVars varType).run used
        pure (lctx, localInsts, newVars.push var, used)
      else
        pure (lctx.erase var.fvarId!, localInsts.erase var.fvarId!, newVars, used))
    (lctx, localInsts, #[], used)
  pure (lctx, localInsts, newVars.reverse)

end Lean.Elab.Term
