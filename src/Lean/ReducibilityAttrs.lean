/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.ScopedEnvExtension
public section
namespace Lean

/--
Reducibility status for a definition. Controls when `isDefEq` and `whnf` are allowed to unfold it.
See `TransparencyMode` for the full design rationale.

- **`reducible`**: Unfolded at `TransparencyMode.reducible` or above. Reducible definitions still
  appear in user-facing terms, but are eagerly unfolded when indexing terms into discrimination
  trees (`simp`, type class resolution) and in `grind`. Think of it as `[inline]` for indexing.
  Suitable for abbreviations and definitions that should be transparent to proof automation.
- **`implicitReducible`**: Unfolded at `TransparencyMode.instances` or above. Used for type class
  instances and definitions that appear in types matched during implicit argument resolution
  (e.g., `Nat.add`, `Array.size`). These definitions cannot be eagerly reduced (instances expand
  into large terms, recursive definitions are problematic), but must be unfoldable when checking
  implicit arguments and resolving instance diamonds (e.g., `Add Nat` via direct instance vs via
  `Semiring`). The attribute `[implicit_reducible]` (or its alias `[instance_reducible]`) marks
  a definition with this status.
- **`semireducible`**: The default. Unfolded at `TransparencyMode.default` or above. Used for
  ordinary definitions. Suitable for user-written code where `isDefEq` should try hard during
  type checking, but not during speculative proof automation.
- **`irreducible`**: Only unfolded at `TransparencyMode.all`. The definition body is effectively
  hidden from `isDefEq` in normal usage.
-/
inductive ReducibilityStatus where
  | reducible | semireducible | irreducible | implicitReducible
  deriving Inhabited, Repr, BEq

def ReducibilityStatus.toAttrString : ReducibilityStatus → String
  | .reducible => "[reducible]"
  | .irreducible => "[irreducible]"
  | .semireducible => "[semireducible]"
  | .implicitReducible => "[implicit_reducible]"

builtin_initialize reducibilityCoreExt : PersistentEnvExtension (Name × ReducibilityStatus) (Name × ReducibilityStatus) (NameMap ReducibilityStatus) ←
  registerPersistentEnvExtension {
    name            := `reducibilityCore
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun (s : NameMap ReducibilityStatus) (p : Name × ReducibilityStatus) => s.insert p.1 p.2
    exportEntriesFn := fun m =>
      let r : Array (Name × ReducibilityStatus) := m.foldl (fun a n p => a.push (n, p)) #[]
      r.qsort (fun a b => Name.quickLt a.1 b.1)
    statsFn         := fun s => "reducibility attribute core extension" ++ Format.line ++ "number of local entries: " ++ format s.size
    -- attribute is set by `addPreDefinitions`
    asyncMode       := .async .asyncEnv
    replay? := some <| fun _oldState newState newItems otherState =>
      newItems.foldl (init := otherState) fun otherState k =>
        if let some v := newState.find? k then
          otherState.insert k v
        else
          otherState
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
  | none => (reducibilityCoreExt.getState (asyncDecl := declName) env).find? declName |>.getD .semireducible

private def setReducibilityStatusCore (env : Environment) (declName : Name) (status : ReducibilityStatus) (attrKind : AttributeKind) (currNamespace : Name) : Environment :=
  if attrKind matches .global then
    match env.getModuleIdxFor? declName with
    | some _ =>
      -- Trying to set the attribute of a declaration defined in an imported module.
      reducibilityExtraExt.addEntry env (declName, status)
    | none =>
      let _ : Inhabited Environment := ⟨env⟩
      reducibilityCoreExt.addEntry (asyncDecl := declName) env (declName, status)
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
  let suffix := .note "Use `set_option allowUnsafeReducibility true` to override reducibility status validation"
  -- Allow global visibility attributes even on non-exported definitions - they may be relevant for
  -- downstream non-`module`s.
  withoutExporting do
  unless allowUnsafeReducibility.get (← getOptions) do
    unless (← getConstInfo declName).isDefinition do
      throwError "failed to set reducibility status, `{.ofConstName declName}` is not a definition{suffix}"
    let statusOld := getReducibilityStatusCore (← getEnv) declName
    match attrKind with
    | .scoped =>
      throwError "failed to set reducibility status for `{.ofConstName declName}`, the `scoped` modifier is not recommended for this kind of attribute{suffix}"
    | .global =>
      if (← getEnv).getModuleIdxFor? declName matches some _ then
        throwError "failed to set reducibility status, `{.ofConstName declName}` has not been defined in this file, consider using the `local` modifier{suffix}"
      match status with
      | .reducible =>
        unless statusOld matches .semireducible do
          throwError "failed to set `[reducible]`, `{.ofConstName declName}` is not currently `[semireducible]`, but `{statusOld.toAttrString}`{suffix}"
      | .irreducible =>
        unless statusOld matches .semireducible | .implicitReducible do
          throwError "failed to set `[irreducible]`, `{.ofConstName declName}` is not currently `[semireducible]` nor `[implicit_reducible]`, but `{statusOld.toAttrString}`{suffix}"
      | .implicitReducible =>
        unless statusOld matches .semireducible do
          throwError "failed to set `[implicit_reducible]`, `{.ofConstName declName}` is not currently `[semireducible]`, but `{statusOld.toAttrString}`{suffix}"
      | .semireducible =>
        throwError "failed to set `[semireducible]` for `{.ofConstName declName}`, declarations are `[semireducible]` by default{suffix}"
    | .local =>
      match status with
      | .reducible =>
        throwError "failed to set `[local reducible]` for `{.ofConstName declName}`, recall that `[reducible]` affects the term indexing datastructures used by `simp` and type class resolution{suffix}"
      | .irreducible =>
        unless statusOld matches .semireducible | .implicitReducible do
          throwError "failed to set `[local irreducible]`, `{.ofConstName declName}` is currently `{statusOld.toAttrString}`, `[semireducible]` nor `[implicit_reducible]` expected{suffix}"
      | .implicitReducible =>
        unless statusOld matches .semireducible do
          throwError "failed to set `[local implicit_reducible]`, `{.ofConstName declName}` is currently `{statusOld.toAttrString}`, `[semireducible]` expected{suffix}"
      | .semireducible =>
        unless statusOld matches .irreducible do
          throwError "failed to set `[local semireducible]`, `{.ofConstName declName}` is currently `{statusOld.toAttrString}`, `[irreducible]` expected{suffix}"

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

/--
Marks a definition as `[implicit_reducible]`, meaning it is unfolded at
`TransparencyMode.instances` or above but *not* at `TransparencyMode.reducible`.

Use this attribute for:
- **Type class instances**: The `instance` command automatically adds `[implicit_reducible]`.
  Instance diamonds (e.g., `Add Nat` from a direct instance vs via `Semiring`) are definitionally
  equal but structurally different, so `isDefEq` must unfold them. When using `attribute [instance]`
  on an existing definition, you typically also need `attribute [implicit_reducible]`.
- **Definitions used in types that appear in implicit arguments**: For example, `Nat.add`, `Array.size`.
  When proof automation applies a lemma, implicit arguments are checked with increased transparency
  so that type-level computations (e.g., `n + 0` vs `n`) are resolved.

`[instance_reducible]` is an alias for this attribute.
-/
builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `implicit_reducible
    descr           := "implicit reducible declaration"
    add             := addAttr .implicitReducible
    applicationTime := .afterTypeChecking
 }

/-- Alias for `[implicit_reducible]`. See `implicit_reducible` for documentation. -/
builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `instance_reducible
    descr           := "alias for implicit_reducible"
    add             := addAttr .implicitReducible
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
  return (← getReducibilityStatus declName) matches .reducible

/-- Return `true` if the given declaration has been marked as `[irreducible]` -/
def isIrreducible [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  return (← getReducibilityStatus declName) matches .irreducible

def isImplicitReducibleCore (env : Environment) (declName : Name) : Bool :=
  getReducibilityStatusCore env declName matches .implicitReducible

/-- Return `true` if the given declaration has been marked as `[implicit_reducible]`. -/
def isImplicitReducible [Monad m] [MonadEnv m] (declName : Name) : m Bool :=
  return isImplicitReducibleCore (← getEnv) declName

@[deprecated isImplicitReducibleCore (since := "2026-02-18")] abbrev isInstanceReducibleCore := isImplicitReducibleCore
@[deprecated isImplicitReducible (since := "2026-02-18")] abbrev isInstanceReducible := @isImplicitReducible

/-- Set the given declaration as `[irreducible]` -/
def setIrreducibleAttribute [MonadEnv m] (declName : Name) : m Unit :=
  setReducibilityStatus declName ReducibilityStatus.irreducible

end Lean
