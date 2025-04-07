/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Attributes
import Lean.ScopedEnvExtension

namespace Lean

/--
Reducibility status for a definition.
-/
inductive ReducibilityStatus where
  | reducible | semireducible | irreducible
  deriving Inhabited, Repr, BEq

def ReducibilityStatus.toAttrString : ReducibilityStatus → String
  | .reducible => "[reducible]"
  | .irreducible => "[irreducible]"
  | .semireducible => "[semireducible]"

builtin_initialize reducibilityCoreExt : PersistentEnvExtension (Name × ReducibilityStatus) (Name × ReducibilityStatus) (NameMap ReducibilityStatus) ←
  registerPersistentEnvExtension {
    name            := `reducibilityCore
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun (s : NameMap ReducibilityStatus) (p : Name × ReducibilityStatus) => s.insert p.1 p.2
    exportEntriesFn := fun m =>
      let r : Array (Name × ReducibilityStatus) := m.fold (fun a n p => a.push (n, p)) #[]
      r.qsort (fun a b => Name.quickLt a.1 b.1)
    statsFn         := fun s => "reducibility attribute core extension" ++ Format.line ++ "number of local entries: " ++ format s.size
    asyncMode       := .async
  }

builtin_initialize reducibilityExtraExt : SimpleScopedEnvExtension (Name × ReducibilityStatus) (SMap Name ReducibilityStatus) ←
  registerSimpleScopedEnvExtension {
    name := `reducibilityExtra
    initial := {}
    addEntry := fun d (declName, status) => d.insert declName status
    finalizeImport := fun d => d.switch
  }

@[export lean_get_reducibility_status]
def getReducibilityStatusCore (env : Environment) (declName : Name) : ReducibilityStatus :=
  let m := reducibilityExtraExt.getState env
  if let some status := m.find? declName then
    status
  else match env.getModuleIdxFor? declName with
  | some modIdx =>
    match (reducibilityCoreExt.getModuleEntries env modIdx).binSearch (declName, .semireducible) (fun a b => Name.quickLt a.1 b.1) with
    | some (_, status) => status
    | none => .semireducible
  | none => (reducibilityCoreExt.findStateAsync env declName).find? declName |>.getD .semireducible

private def setReducibilityStatusCore (env : Environment) (declName : Name) (status : ReducibilityStatus) (attrKind : AttributeKind) (currNamespace : Name) : Environment :=
  if attrKind matches .global then
    match env.getModuleIdxFor? declName with
    | some _ =>
      -- Trying to set the attribute of a declaration defined in an imported module.
      reducibilityExtraExt.addEntry env (declName, status)
    | none =>
      let _ : Inhabited Environment := ⟨env⟩
      assert! env.asyncMayContain declName
      reducibilityCoreExt.addEntry env (declName, status)
  else
    -- `scoped` and `local` must be handled by `reducibilityExtraExt`
    reducibilityExtraExt.addCore env (declName, status) attrKind currNamespace

@[export lean_set_reducibility_status]
private def setReducibilityStatusImp (env : Environment) (declName : Name) (status : ReducibilityStatus) : Environment :=
  setReducibilityStatusCore env declName status .global .anonymous

/-
TODO: it would be great if we could distinguish between the following two situations

1-
```
@[reducible] def foo := ...
```

2-
```
def foo := ...
...
attribute [reducible] foo
```

Reason: the second one is problematic if user has add simp theorems or TC instances that include `foo`.
Recall that the discrimination trees unfold `[reducible]` declarations while indexing new entries.
-/

register_builtin_option allowUnsafeReducibility : Bool := {
  defValue := false
  descr    := "enables users to modify the reducibility settings for declarations even when such changes are deemed potentially hazardous. For example, `simp` and type class resolution maintain term indices where reducible declarations are expanded."
}

private def validate (declName : Name) (status : ReducibilityStatus) (attrKind : AttributeKind) : CoreM Unit := do
  let suffix := "use `set_option allowUnsafeReducibility true` to override reducibility status validation"
  unless allowUnsafeReducibility.get (← getOptions) do
    match (← getConstInfo declName) with
    | .defnInfo _ =>
      let statusOld := getReducibilityStatusCore (← getEnv) declName
      match attrKind with
      | .scoped =>
        throwError "failed to set reducibility status for `{declName}`, the `scoped` modifier is not recommended for this kind of attribute\n{suffix}"
      | .global =>
        if (← getEnv).getModuleIdxFor? declName matches some _ then
          throwError "failed to set reducibility status, `{declName}` has not been defined in this file, consider using the `local` modifier\n{suffix}"
        match status with
        | .reducible =>
          unless statusOld matches .semireducible do
            throwError "failed to set `[reducible]`, `{declName}` is not currently `[semireducible]`, but `{statusOld.toAttrString}`\n{suffix}"
        | .irreducible =>
          unless statusOld matches .semireducible do
            throwError "failed to set `[irreducible]`, `{declName}` is not currently `[semireducible]`, but `{statusOld.toAttrString}`\n{suffix}"
        | .semireducible =>
          throwError "failed to set `[semireducible]` for `{declName}`, declarations are `[semireducible]` by default\n{suffix}"
      | .local =>
        match status with
        | .reducible =>
          throwError "failed to set `[local reducible]` for `{declName}`, recall that `[reducible]` affects the term indexing datastructures used by `simp` and type class resolution\n{suffix}"
        | .irreducible =>
          unless statusOld matches .semireducible do
            throwError "failed to set `[local irreducible]`, `{declName}` is currently `{statusOld.toAttrString}`, `[semireducible]` expected\n{suffix}"
        | .semireducible =>
          unless statusOld matches .irreducible do
            throwError "failed to set `[local semireducible]`, `{declName}` is currently `{statusOld.toAttrString}`, `[irreducible]` expected\n{suffix}"
    | _ => throwError "failed to set reducibility status, `{declName}` is not a definition\n{suffix}"

private def addAttr (status : ReducibilityStatus) (declName : Name) (stx : Syntax) (attrKind : AttributeKind) : AttrM Unit := do
  Attribute.Builtin.ensureNoArgs stx
  validate declName status attrKind
  let ns ← getCurrNamespace
  modifyEnv fun env => setReducibilityStatusCore env declName status attrKind ns

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `irreducible
    descr           := "irreducible declaration"
    add             := addAttr .irreducible
    applicationTime := .afterTypeChecking
 }

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `reducible
    descr           := "reducible declaration"
    add             := addAttr .reducible
    applicationTime := .afterTypeChecking
 }

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `semireducible
    descr           := "semireducible declaration"
    add             := addAttr .semireducible
    applicationTime := .afterTypeChecking
 }

/-- Return the reducibility attribute for the given declaration. -/
def getReducibilityStatus [Monad m] [MonadEnv m] (declName : Name) : m ReducibilityStatus := do
  return getReducibilityStatusCore (← getEnv) declName

/-- Set the reducibility attribute for the given declaration. -/
def setReducibilityStatus [MonadEnv m] (declName : Name) (s : ReducibilityStatus) : m Unit :=
  modifyEnv fun env => setReducibilityStatusCore env declName s .global .anonymous

/-- Set the given declaration as `[reducible]` -/
def setReducibleAttribute [MonadEnv m] (declName : Name) : m Unit :=
  setReducibilityStatus declName ReducibilityStatus.reducible

/-- Return `true` if the given declaration has been marked as `[reducible]`. -/
def isReducible [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  match (← getReducibilityStatus declName) with
  | .reducible => return true
  | _ => return false

/-- Return `true` if the given declaration has been marked as `[irreducible]` -/
def isIrreducible [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  match (← getReducibilityStatus declName) with
  | .irreducible => return true
  | _ => return false

/-- Set the given declaration as `[irreducible]` -/
def setIrreducibleAttribute [MonadEnv m] (declName : Name) : m Unit :=
  setReducibilityStatus declName ReducibilityStatus.irreducible


end Lean
