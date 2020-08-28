/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.CollectMVars
import Lean.Meta.Basic

namespace Lean
namespace Meta

/--
  Collect unassigned metavariables occuring in the given expression.

  Remark: if `e` contains `?m` and there is a `t` assigned to `?m`, we
  collect unassigned metavariables occurring in `t`.

  Remark: if `e` contains `?m` and `?m` is delayed assigned to some term `t`,
  we collect `?m` and unassigned metavariables occurring in `t`.
  We collect `?m` because it has not been assigned yet. -/
partial def collectMVarsAux : Expr → StateRefT CollectMVars.State MetaM Unit
| e => do
  e ← instantiateMVars e;
  s ← get;
  let resultSavedSize := s.result.size;
  let s := e.collectMVars s;
  set s;
  s.result.forFromM
    (fun mvarId => do
      d? ← getDelayedAssignment? mvarId;
      match d? with
      | none   => pure ()
      | some d => collectMVarsAux d.val)
    resultSavedSize

def collectMVars (e : Expr) : StateRefT CollectMVars.State MetaM Unit :=
collectMVarsAux e

variables {m : Type → Type} [MonadLiftT MetaM m]

def getMVarsImp (e : Expr) : MetaM (Array MVarId) := do
(_, s) ← (collectMVars e).run {};
pure s.result

/-- Return metavariables in occuring the given expression. See `collectMVars` -/
def getMVars (e : Expr) : m (Array MVarId) :=
liftM $ getMVarsImp e

def getMVarsNoDelayedImp (e : Expr) : MetaM (Array MVarId) := do
mvarIds ← getMVars e;
mvarIds.filterM fun mvarId => not <$> isDelayedAssigned mvarId

/-- Similar to getMVars, but removes delayed assignments. -/
def getMVarsNoDelayed (e : Expr) : m (Array MVarId) :=
liftM $ getMVarsNoDelayedImp e

def collectMVarsAtDecl (d : Declaration) : StateRefT CollectMVars.State MetaM Unit :=
d.forExprM collectMVars

def getMVarsAtDeclImp (d : Declaration) : MetaM (Array MVarId) := do
(_, s) ← (collectMVarsAtDecl d).run {};
pure s.result

def getMVarsAtDecl (d : Declaration) : m (Array MVarId) :=
liftM $ getMVarsAtDeclImp d



end Meta
end Lean
