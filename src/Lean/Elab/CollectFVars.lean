/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectFVars
import Lean.Elab.Term

namespace Lean
namespace Elab
namespace Term

open Meta

def collectUsedFVars (e : Expr) : StateRefT CollectFVars.State TermElabM Unit := do
e ← instantiateMVars e;
modify fun used => collectFVars used e

def collectUsedFVarsAtFVars (fvars : Array Expr) : StateRefT CollectFVars.State TermElabM Unit :=
fvars.forM fun fvar => do
  fvarType ← inferType fvar;
  collectUsedFVars fvarType

def removeUnused (vars : Array Expr) (used : CollectFVars.State) : TermElabM (LocalContext × LocalInstances × Array Expr) := do
localInsts ← getLocalInstances;
lctx ← getLCtx;
(lctx, localInsts, newVars, _) ← vars.foldrM
  (fun var (result : LocalContext × LocalInstances × Array Expr × CollectFVars.State) =>
    let (lctx, localInsts, newVars, used) := result;
    if used.fvarSet.contains var.fvarId! then do
      varType ← inferType var;
      (_, used) ← (collectUsedFVars varType).run used;
      pure (lctx, localInsts, newVars.push var, used)
    else
      pure (lctx.erase var.fvarId!, localInsts.erase var.fvarId!, newVars, used))
  (lctx, localInsts, #[], used);
pure (lctx, localInsts, newVars.reverse)

end Term
end Elab
end Lean
