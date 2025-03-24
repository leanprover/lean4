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
  let _ ← (← reservedNameActionsRef.get).anyM (· name)

/--
Similar to `resolveGlobalName`, but also executes reserved name actions.
-/
def realizeGlobalName (id : Name) : CoreM (List (Name × List String)) := do
  let cs ← resolveGlobalName id
  cs.filterM fun (c, _) => do
    if (← getEnv).contains c then
      return true
    else
      try
        executeReservedNameAction c
        -- note that even if an action "handled" a name, it may still be undefined, e.g. with an
        -- out-of-bounds equation index
        return (← getEnv).containsOnBranch c
      catch ex =>
        -- We record the error produced by the reserved name action generator
        logError m!"Failed to realize constant {id}:{indentD ex.toMessageData}"
        return false

/--
Similar to `resolveGlobalConstCore`, but also executes reserved name actions.
-/
def realizeGlobalConstCore (n : Name) : CoreM (List Name) := do
  let cs ← realizeGlobalName n
  filterFieldList n cs

/--
Similar to `realizeGlobalConstNoOverloadCore`, but also executes reserved name actions.
-/
def realizeGlobalConstNoOverloadCore (n : Name) : CoreM Name := do
  ensureNoOverload n (← realizeGlobalConstCore n)

/--
Similar to `resolveGlobalConst`, but also executes reserved name actions.

Consider using `realizeGlobalConstWithInfo` if you want the syntax to show the resulting name's info
on hover.
-/
def realizeGlobalConst (stx : Syntax) : CoreM (List Name) :=
  withRef stx do preprocessSyntaxAndResolve stx realizeGlobalConstCore

/--
Similar to `realizeGlobalConstNoOverload`, but also executes reserved name actions.

Consider using `realizeGlobalConstNoOverloadWithInfo` if you want the syntax to show the resulting
name's info on hover.
-/
def realizeGlobalConstNoOverload (id : Syntax) : CoreM Name := do
  ensureNonAmbiguous id (← realizeGlobalConst id)

end Lean
