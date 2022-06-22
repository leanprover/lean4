/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectFVars
import Lean.Meta.Basic

namespace Lean

open Meta

def Expr.collectFVars (e : Expr) : StateRefT CollectFVars.State MetaM Unit := do
  let e ← instantiateMVars e
  modify fun used => Lean.collectFVars used e

def LocalDecl.collectFVars (localDecl : LocalDecl) : StateRefT CollectFVars.State MetaM Unit := do
  match localDecl with
  | LocalDecl.cdecl (type := type) .. => type.collectFVars
  | LocalDecl.ldecl (type := type) (value := value) .. => type.collectFVars; value.collectFVars

namespace Meta

def collectUsedFVarsAtFVars (fvars : Array Expr) : StateRefT CollectFVars.State MetaM Unit :=
  fvars.forM fun fvar => do
    let fvarType ← inferType fvar
    fvarType.collectFVars

def removeUnused (vars : Array Expr) (used : CollectFVars.State) : MetaM (LocalContext × LocalInstances × Array Expr) := do
  let localInsts ← getLocalInstances
  let lctx ← getLCtx
  let (lctx, localInsts, newVars, _) ← vars.foldrM
    (fun var (lctx, localInsts, newVars, used) => do
      if used.fvarSet.contains var.fvarId! then
        let varType ← inferType var
        let (_, used) ← varType.collectFVars.run used
        pure (lctx, localInsts, newVars.push var, used)
      else
        pure (lctx.erase var.fvarId!, localInsts.erase var.fvarId!, newVars, used))
    (lctx, localInsts, #[], used)
  pure (lctx, localInsts, newVars.reverse)

end Meta
end Lean
