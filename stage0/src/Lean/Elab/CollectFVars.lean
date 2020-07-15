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

def collectUsedFVars (ref : Syntax) (used : CollectFVars.State) (e : Expr) : TermElabM CollectFVars.State := do
e ← Term.instantiateMVars ref e;
pure $ collectFVars used e

def collectUsedFVarsAtFVars (ref : Syntax) (used : CollectFVars.State) (fvars : Array Expr) : TermElabM CollectFVars.State :=
fvars.foldlM
  (fun used fvar => do
    fvarType ← Term.inferType ref fvar;
    collectUsedFVars ref used fvarType)
  used

def removeUnused (ref : Syntax) (vars : Array Expr) (used : CollectFVars.State) : TermElabM (LocalContext × LocalInstances × Array Expr) := do
localInsts ← Term.getLocalInsts;
lctx ← Term.getLCtx;
(lctx, localInsts, newVars, _) ← vars.foldrM
  (fun var (result : LocalContext × LocalInstances × Array Expr × CollectFVars.State) =>
    let (lctx, localInsts, newVars, used) := result;
    if used.fvarSet.contains var.fvarId! then do
      varType ← Term.inferType ref var;
      used ← Term.collectUsedFVars ref used varType;
      pure (lctx, localInsts, newVars.push var, used)
    else
      pure (lctx.erase var.fvarId!, localInsts.erase var.fvarId!, newVars, used))
  (lctx, localInsts, #[], used);
pure (lctx, localInsts, newVars.reverse)

end Term
end Elab
end Lean
