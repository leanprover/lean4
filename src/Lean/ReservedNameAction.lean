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
The result is `true` if a handler for the given reserved name was found.
Note that the handler can throw an exception.
-/
def executeReservedNameAction (name : Name) : CoreM Bool := do
  for act in (← reservedNameActionsRef.get) do
    if (← act name) then
      return true
  return false

/--
Similar to `resolveGlobalName`, but also executes reserved name actions.
-/
def resolveGlobalName' (id : Name) : CoreM (List (Name × List String)) := do
  let cs ← resolveGlobalName id
  for (c, _) in cs do
    unless (← getEnv).contains c do
      if (← executeReservedNameAction c) then
        unless (← getEnv).contains c do
          throwError "'{id}' is a reserved name, but reserved name code generator failed"
      else
        throwError "'{id}' is a reserved name, but none of the installed reserved name code generators is applicable"
  return cs

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
