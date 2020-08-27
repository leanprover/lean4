/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.CollectMVars
import Lean.Meta.Basic

namespace Lean
namespace Meta

/-- Collect unassigned metavariables -/
def collectMVars (e : Expr) : StateRefT CollectMVars.State MetaM Unit := do
e ← instantiateMVars e;
s ← get;
set $ e.collectMVars s

variables {m : Type → Type} [MonadLiftT MetaM m]

def getMVarsImp (e : Expr) : MetaM (Array MVarId) := do
(_, s) ← (collectMVars e).run {};
pure s.result

def getMVars (e : Expr) : m (Array MVarId) :=
liftM $ getMVarsImp e

def collectMVarsAtDecl (d : Declaration) : StateRefT CollectMVars.State MetaM Unit :=
d.forExprM collectMVars

def getMVarsAtDeclImp (d : Declaration) : MetaM (Array MVarId) := do
(_, s) ← (collectMVarsAtDecl d).run {};
pure s.result

def getMVarsAtDecl (d : Declaration) : m (Array MVarId) :=
liftM $ getMVarsAtDeclImp d

end Meta
end Lean
