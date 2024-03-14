/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.CoreM

namespace Lean

/--
When trying to resolve a reserved name, an action can be executed to generate the actual definition/theorem.
The action returns `true` if it "handled" the given name.

Remark: usually when one install a reserved name predicate, an associated action is also installed.
-/
def ReservedNameAction := Name → CoreM Bool

private builtin_initialize reservedNameActionsRef : IO.Ref (Array ReservedNameAction) ← IO.mkRef #[]

/--
Register a new function that is invoked when trying to resolve a reserved name.
-/
def registerReservedNameAction (act : ReservedNameAction) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register reserved name action, this kind of extension can only be registered during initialization")
  reservedNameActionsRef.modify (·.push act)

/--
Execute a registered reserved action for the given reserved name.
Note that the handler can throw an exception.
-/
def executeReservedNameAction (name : Name) : CoreM Unit := do
  for act in (← reservedNameActionsRef.get) do
    if (← act name) then
      return ()

/--
Similar to `resolveGlobalName`, but also executes reserved name actions.
-/
def resolveGlobalName' (id : Name) : CoreM (List (Name × List String)) := do
  let cs ← resolveGlobalName id
  cs.filterM fun (c, _) => do
    if (← getEnv).contains c then
      return true
    else
      try
        executeReservedNameAction c
        return (← getEnv).contains c
      catch _ =>
        -- TODO: better error handling
        return false

/--
Similar to `resolveGlobalConstCore`, but also executes reserved name actions.
-/
def resolveGlobalConstCore' (n : Name) : CoreM (List Name) := do
  let cs ← resolveGlobalName' n
  filterFieldList n cs

/--
Similar to `resolveGlobalConstNoOverloadCore`, but also executes reserved name actions.
-/
def resolveGlobalConstNoOverloadCore' (n : Name) : CoreM Name := do
  ensureNoOverload n (← resolveGlobalConstCore' n)

/--
Similar to `resolveGlobalConst`, but also executes reserved name actions.
-/
def resolveGlobalConst' (stx : Syntax) : CoreM (List Name) :=
  preprocessSyntaxAndResolve stx resolveGlobalConstCore'

/--
Similar to `resolveGlobalConstNoOverload`, but also executes reserved name actions.
-/
def resolveGlobalConstNoOverload' (id : Syntax) : CoreM Name := do
  ensureNonAmbiguous id (← resolveGlobalConst' id)

end Lean
