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
- **`instanceReducible`**: Unfolded at `TransparencyMode.instances` or above. Auto-applied by the
  `instance` command and to subobject projections of class parents. The attribute
  `[instance_reducible]` marks a definition with this status; users typically do not need to
  apply it manually.
- **`implicitReducible`**: Unfolded at `TransparencyMode.implicit` or above (strictly above
  `.instances`). Used for definitions that should unfold when checking implicit and
  instance-implicit arguments for definitional equality, including for resolving instance diamonds,
  but must stay opaque to type class *search*.
  The attribute `[implicit_reducible]` marks a definition with this status.
  (Note: core arithmetic such as `Nat.add` and `Array.size` is deliberately `instanceReducible`,
  not `implicitReducible`, because type class synthesis depends on it unfolding.)
- **`semireducible`**: The default. Unfolded at `TransparencyMode.default` or above. Used for
  ordinary definitions. Suitable for user-written code where `isDefEq` should try hard during
  type checking, but not during speculative proof automation.
- **`irreducible`**: Only unfolded at `TransparencyMode.all`. The definition body is effectively
  hidden from `isDefEq` in normal usage.
-/
-- Note: `implicitReducible` and `instanceReducible` appear last for the same reason
-- `TransparencyMode`'s constructors are not in unfolding order: reordering them causes a
-- non-trivial bootstrapping problem.
inductive ReducibilityStatus where
  | reducible | semireducible | irreducible | implicitReducible | instanceReducible
  deriving Inhabited, Repr, BEq

def ReducibilityStatus.toAttrString : ReducibilityStatus → String
  | .reducible => "[reducible]"
  | .irreducible => "[irreducible]"
  | .semireducible => "[semireducible]"
  | .implicitReducible => "[implicit_reducible]"
  | .instanceReducible => "[instance_reducible]"

builtin_initialize reducibilityCoreExt : PersistentEnvExtension (Name × ReducibilityStatus) (Name × ReducibilityStatus) (NameMap ReducibilityStatus) ←
  registerPersistentEnvExtension {
    name            := `reducibilityCore
    -- resolution-path reads are recorded per declaration by `getReducibilityStatusCore`
    tcResolutionAccess := .exempt
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
    -- resolution-path reads are recorded per declaration by `getReducibilityStatusCore`
    tcResolutionAccess := .exempt
    initial := {}
    addEntry := fun d (declName, status) => d.insert declName status
    finalizeImport := fun d => d.switch
  }

/--
Change counter for reducibility statuses, bumped by every reducibility attribute application
(including scoped and local ones). A type class resolution query captures its value when it
starts (`SynthEnvDeps.reducibilityGen`); while it is unchanged, the per-declaration statuses a
cache entry recorded cannot have changed, so validation skips re-asking them and the entry
revalidates with a single comparison. When the counter has moved, validation re-asks each
recorded status (`validReducibilityDeps`) and, on success, re-stamps the entry with the current
value.

Branch-local (`AsyncMode.local`), like the resolution cache itself. Declaration-time status
assignments via `setReducibilityStatus` do not bump it: a declaration's initial status cannot be
recorded in any pre-existing cache entry, as no query can have asked about the declaration
before it existed.
-/
builtin_initialize reducibilityChangedExt : EnvExtension Unit ←
  registerEnvExtension (pure ()) (asyncMode := .local) (name := `reducibilityChanged)
    (tcResolutionAccess := .recorded)

/-- Stable encoding of `ReducibilityStatus` for `SynthEnvDeps.reducibility`. -/
private def statusIdx : ReducibilityStatus → Nat
  | .reducible         => 0
  | .semireducible     => 1
  | .irreducible       => 2
  | .implicitReducible => 3
  | .instanceReducible => 4

private unsafe def recordStatusUnsafe (env : Environment) (declName : Name) (status : ReducibilityStatus) : ReducibilityStatus :=
  match env.synthEnvDepsRef? with
  | none => status
  | some sink =>
    -- benign effect: recording the observed status into the armed query's accumulator
    unsafeBaseIO do
      sink.modify fun d =>
        if d.reducibility.contains declName then d
        else { d with reducibility := d.reducibility.insert declName (statusIdx status) }
      return status

/--
Records `declName ↦ status` as a dependency of the type class resolution query in progress, if
any; see `reducibilityChangedExt`. Returns `status` so the recording cannot be optimized away.
-/
@[implemented_by recordStatusUnsafe]
private opaque recordStatus (env : Environment) (declName : Name) (status : ReducibilityStatus) : ReducibilityStatus

def getReducibilityStatusCore (env : Environment) (declName : Name) : ReducibilityStatus :=
  let status :=
    let m := reducibilityExtraExt.getState env
    if let some status := m.find? declName then
      status
    else match env.getModuleIdxFor? declName with
    | some modIdx =>
      match (reducibilityCoreExt.getModuleEntries env modIdx).binSearch (declName, .semireducible) (fun a b => Name.quickLt a.1 b.1) with
      | some (_, status) => status
      | none => .semireducible
    | none => (reducibilityCoreExt.getState (asyncDecl := declName) env).find? declName |>.getD .semireducible
  recordStatus env declName status

/--
Returns whether every reducibility status recorded in `deps` gives the same answer in `env`.
Used to validate a type class resolution cache entry once the reducibility change counter has
moved; see `reducibilityChangedExt`.
-/
def validReducibilityDeps (env : Environment) (deps : NameMap Nat) : Bool :=
  deps.all fun declName idx => statusIdx (getReducibilityStatusCore env declName) == idx

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
        unless statusOld matches .semireducible | .implicitReducible | .instanceReducible do
          throwError "failed to set `[irreducible]`, `{.ofConstName declName}` is not currently `[semireducible]`, `[implicit_reducible]` nor `[instance_reducible]`, but `{statusOld.toAttrString}`{suffix}"
      | .implicitReducible =>
        -- Allow `[semireducible] -> [implicit_reducible]` and the upgrade
        -- `[instance_reducible] -> [implicit_reducible]` (so instances can be strengthened to
        -- only unfold during implicit-arg defeq).
        unless statusOld matches .semireducible | .instanceReducible do
          throwError "failed to set `[implicit_reducible]`, `{.ofConstName declName}` is not currently `[semireducible]` nor `[instance_reducible]`, but `{statusOld.toAttrString}`{suffix}"
      | .instanceReducible =>
        unless statusOld matches .semireducible do
          throwError "failed to set `[instance_reducible]`, `{.ofConstName declName}` is not currently `[semireducible]`, but `{statusOld.toAttrString}`{suffix}"
      | .semireducible =>
        if statusOld matches .semireducible then do
          throwError "failed to set `[semireducible]` for `{.ofConstName declName}` because it already is `[semireducible]`{suffix}"
        else
          throwError "failed to set `[semireducible]` for `{.ofConstName declName}`{suffix}"
    | .local =>
      match status with
      | .reducible =>
        throwError "failed to set `[local reducible]` for `{.ofConstName declName}`, recall that `[reducible]` affects the term indexing datastructures used by `simp` and type class resolution{suffix}"
      | .irreducible =>
        unless statusOld matches .semireducible | .implicitReducible | .instanceReducible do
          throwError "failed to set `[local irreducible]`, `{.ofConstName declName}` is currently `{statusOld.toAttrString}`, `[semireducible]`, `[implicit_reducible]` nor `[instance_reducible]` expected{suffix}"
      | .implicitReducible =>
        unless statusOld matches .semireducible | .instanceReducible do
          throwError "failed to set `[local implicit_reducible]`, `{.ofConstName declName}` is currently `{statusOld.toAttrString}`, `[semireducible]` or `[instance_reducible]` expected{suffix}"
      | .instanceReducible =>
        unless statusOld matches .semireducible do
          throwError "failed to set `[local instance_reducible]`, `{.ofConstName declName}` is currently `{statusOld.toAttrString}`, `[semireducible]` expected{suffix}"
      | .semireducible =>
        unless statusOld matches .irreducible do
          throwError "failed to set `[local semireducible]`, `{.ofConstName declName}` is currently `{statusOld.toAttrString}`, `[irreducible]` expected{suffix}"

private def addAttr (status : ReducibilityStatus) (declName : Name) (stx : Syntax) (attrKind : AttributeKind) : AttrM Unit := do
  Attribute.Builtin.ensureNoArgs stx
  validate declName status attrKind
  let ns ← getCurrNamespace
  modifyEnv fun env => setReducibilityStatusCore env declName status attrKind ns
  -- Reducibility determines what `isDefEq` may unfold, so a status change can invalidate cached
  -- type class resolution results computed under the old status. Bumping the change counter
  -- makes cache entries re-validate their recorded statuses on next use; see
  -- `reducibilityChangedExt`.
  modifyEnv (reducibilityChangedExt.modifyState · id)

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
`TransparencyMode.implicit` or above but *not* at `TransparencyMode.instances` or
`TransparencyMode.reducible`.

Use this attribute for definitions that should unfold when checking implicit-argument
definitional equality (e.g. abbreviations in downstream libraries such as Mathlib functors),
without affecting type class search. When proof automation applies a lemma, implicit arguments
are checked with increased transparency so that type-level computations (e.g. `n + 0` vs `n`)
are resolved.

To mark a potential *type class instance* — so it can be unfolded during type class synthesis —
use `[instance_reducible]` instead (which the `instance` command applies automatically).
-/
builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `implicit_reducible
    descr           := "implicit reducible declaration"
    add             := addAttr .implicitReducible
    applicationTime := .afterTypeChecking
 }

/--
Marks a definition as `[instance_reducible]`, meaning it is unfolded at
`TransparencyMode.instances` or above but *not* at `TransparencyMode.reducible`.

Applied to type class instances and instance-like support symbols (e.g., subobject projections
to class parents). The `instance` command automatically adds `[instance_reducible]`.

Applying `[implicit_reducible]` to an `[instance_reducible]` declaration moves it to the higher
implicit reducibility level; it will no longer unfold at `.instances` transparency.
-/
builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `instance_reducible
    descr           := "instance reducible declaration"
    add             := addAttr .instanceReducible
    applicationTime := .afterTypeChecking
 }

/-- Return the reducibility attribute for the given declaration. -/
def getReducibilityStatus [Monad m] [MonadEnv m] (declName : Name) : m ReducibilityStatus := do
  return getReducibilityStatusCore (← getEnv) declName

/--
Set the reducibility attribute for the given declaration.

Note: does not bump the reducibility change counter (`reducibilityChangedExt`). Use only for
declarations created by the caller itself (before other code can have cached results about
them); status changes to pre-existing declarations must go through the reducibility attributes.
-/
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

def isInstanceReducibleCore (env : Environment) (declName : Name) : Bool :=
  getReducibilityStatusCore env declName matches .instanceReducible

/-- Return `true` if the given declaration has been marked as `[instance_reducible]`
(automatically applied by the `instance` command and by subobject class projections). -/
def isInstanceReducible [Monad m] [MonadEnv m] (declName : Name) : m Bool :=
  return isInstanceReducibleCore (← getEnv) declName

/-- Set the given declaration as `[irreducible]` -/
def setIrreducibleAttribute [MonadEnv m] (declName : Name) : m Unit :=
  setReducibilityStatus declName ReducibilityStatus.irreducible

end Lean
