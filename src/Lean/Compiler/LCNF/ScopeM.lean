/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF

/--
A general abstraction for the idea of a scope in the compiler.
-/
abbrev ScopeM := StateRefT FVarIdSet CompilerM

namespace ScopeM

def getScope : ScopeM FVarIdSet := get
def setScope (newScope : FVarIdSet) : ScopeM Unit := set newScope
def clearScope : ScopeM Unit := setScope {}

/--
Execute `x` but recover the previous scope after doing so.
-/
def withBackTrackingScope [MonadLiftT ScopeM m] [Monad m] [MonadFinally m] (x : m α) : m α := do
  let scope ← getScope
  try x finally setScope scope

/--
Clear the current scope for the monadic action `x`, afterwards continuing
with the old one.
-/
def withNewScope [MonadLiftT ScopeM m] [Monad m] [MonadFinally m] (x : m α) : m α := do
  withBackTrackingScope do
    clearScope
    x

/--
Check whether `fvarId` is in the current scope, that is, was declared within
the current `fun` declaration that is being processed.
-/
def isInScope (fvarId : FVarId) : ScopeM Bool := do
  let scope ← getScope
  return scope.contains fvarId

/--
Add a new `FVarId` to the current scope.
-/
def addToScope (fvarId : FVarId) : ScopeM Unit :=
  modify fun scope => scope.insert fvarId

end ScopeM

end Lean.Compiler.LCNF
