/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Basic

namespace Lean.Compiler.LCNF

abbrev Scope := FVarIdSet

class MonadScope (m : Type → Type) where
  getScope : m Scope
  withScope : (Scope → Scope) → m α → m α

export MonadScope (getScope withScope)

abbrev ScopeT (m : Type → Type) := ReaderT Scope m

instance [Monad m] : MonadScope (ScopeT m) where
  getScope  := read
  withScope := withReader

instance (m n) [MonadLift m n] [MonadFunctor m n] [MonadScope m] : MonadScope n where
  getScope    := liftM (getScope : m _)
  withScope f := monadMap (m := m) (withScope f)

def inScope [MonadScope m] [Monad m] (fvarId : FVarId) : m Bool :=
  return (← getScope).contains fvarId

@[inline] def withParams [MonadScope m] [Monad m] (ps : Array Param) (x : m α) : m α :=
  withScope (fun s => ps.foldl (init := s) fun s p => s.insert p.fvarId) x

@[inline] def withFVar [MonadScope m] [Monad m] (fvarId : FVarId) (x : m α) : m α :=
  withScope (fun s => s.insert fvarId) x

@[inline] def withNewScope [MonadScope m] [Monad m] (x : m α) : m α := do
  withScope (fun _ => {}) x

end Lean.Compiler.LCNF