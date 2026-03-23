/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Attributes

public section

namespace Lean

namespace ScopedEnvExtension

inductive Entry (α : Type) where
  | global : α → Entry α
  | scoped : Name → α → Entry α

structure ScopedEntries (β : Type) where
  map : SMap Name (PArray β) := {}
  deriving Inhabited

structure StateStack (α : Type) (β : Type) (σ : Type) where
  stateStack    : List σ := []
  scopedEntries : ScopedEntries β := {}
  newEntries    : List (Entry α) := []
  activeScopes  : NameSet := {}
  deriving Inhabited

structure Descr (α : Type) (β : Type) (σ : Type) where
  name           : Name := by exact decl_name%
  mkInitial      : IO σ
  ofOLeanEntry   : σ → α → ImportM β
  toOLeanEntry   : β → α
  addEntry       : σ → β → σ
  finalizeImport : σ → σ := id
  exportEntry?   : OLeanLevel → α → Option α := fun _ => some

instance [Inhabited α] : Inhabited (Descr α β σ) where
  default := {
    name         := default
    mkInitial    := default
    ofOLeanEntry := default
    toOLeanEntry := default
    addEntry     := fun s _ => s
  }

def mkInitial (descr : Descr α β σ) : IO (StateStack α β σ) :=
  return { stateStack := [ (← descr.mkInitial) ] }

def ScopedEntries.insert (scopedEntries : ScopedEntries β) (ns : Name) (b : β) : ScopedEntries β :=
  match scopedEntries.map.find? ns with
  | none    => { map := scopedEntries.map.insert ns <| ({} : PArray β).push b }
  | some bs => { map := scopedEntries.map.insert ns <| bs.push b }

def addImportedFn (descr : Descr α β σ) (as : Array (Array (Entry α))) : ImportM (StateStack α β σ) := do
  let mut s ← descr.mkInitial
  let mut scopedEntries : ScopedEntries β := {}
  for a in as do
    for e in a do
      match e with
      | Entry.global a =>
        let b ← descr.ofOLeanEntry s a
        s := descr.addEntry s b
      | Entry.scoped ns a =>
        let b ← descr.ofOLeanEntry s a
        scopedEntries := scopedEntries.insert ns b
  s := descr.finalizeImport s
  return { stateStack := [ s ], scopedEntries := scopedEntries }

def addEntryFn (descr : Descr α β σ) (s : StateStack α β σ) (e : Entry β) : StateStack α β σ :=
  match s with
  | { stateStack, scopedEntries, newEntries, activeScopes } =>
    match e with
    | Entry.global b => {
        scopedEntries
        activeScopes
        stateStack
        newEntries    := (Entry.global (descr.toOLeanEntry b)) :: newEntries
      }
    | Entry.«scoped» ns b =>
      {
        scopedEntries := scopedEntries.insert ns b
        activeScopes
        stateStack
        newEntries    := (Entry.«scoped» ns (descr.toOLeanEntry b)) :: newEntries
      }

def exportEntriesFn (descr : Descr α β σ) (level : OLeanLevel) (s : StateStack α β σ) : Array (Entry α) :=
  s.newEntries.toArray.reverse.filterMap fun
    | .global e => .global <$> descr.exportEntry? level e
    | .scoped ns e => .scoped ns <$> descr.exportEntry? level e

end ScopedEnvExtension

open ScopedEnvExtension

/-- Centralized scope frame for all ScopedEnvExtensions.
    Each frame snapshots the per-extension states at a scope boundary. -/
structure ScopeFrame where
  /-- Per-extension state snapshots, keyed by EnvExtension idx. -/
  states : Lean.PersistentHashMap Nat EnvExtensionState := {}
  activeScopes : NameSet := {}
  delimitsLocal : Bool := true
  deriving Inhabited

/-- Centralized scope stack state shared by all ScopedEnvExtensions. -/
structure ScopeStackState where
  /-- Current live states for all scoped extensions, keyed by EnvExtension idx. -/
  currentStates : Lean.PersistentHashMap Nat EnvExtensionState := {}
  /-- Current active scopes. -/
  activeScopes : NameSet := {}
  /-- Whether the current scope delimits local entries. -/
  delimitsLocal : Bool := true
  /-- Saved scope frames (outer scopes). -/
  frames : List ScopeFrame := []
  deriving Inhabited

/-- The centralized scope stack extension, registered at init time. -/
builtin_initialize scopeStackExt : EnvExtension ScopeStackState ←
  registerEnvExtension (pure {}) (asyncMode := .local)

structure ScopedEnvExtension (α : Type) (β : Type) (σ : Type) where
  descr : Descr α β σ
  ext   : PersistentEnvExtension (Entry α) (Entry β) (StateStack α β σ)
  deriving Inhabited

builtin_initialize scopedEnvExtensionsRef : IO.Ref (Array (ScopedEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)) ← IO.mkRef #[]

unsafe def registerScopedEnvExtensionUnsafe (descr : Descr α β σ) : IO (ScopedEnvExtension α β σ) := do
  let ext ← registerPersistentEnvExtension {
    name            := descr.name
    mkInitial       := mkInitial descr
    addImportedFn   := addImportedFn descr
    addEntryFn      := addEntryFn descr
    exportEntriesFnEx := fun _ s level => exportEntriesFn descr level s
    statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
    -- We restrict addition of global and `scoped` entries to the main thread but allow addition of
    -- scopes and local entries in any thread, which are visible only in that thread (see uses of
    -- `AsyncMode.local` below). Allowing the latter is important for tactics such as -- `classical`
    -- or `open in`.
    asyncMode       := .mainOnly
  }
  let ext := { descr := descr, ext := ext : ScopedEnvExtension α β σ }
  scopedEnvExtensionsRef.modify fun exts => exts.push (unsafeCast ext)
  return ext

@[implemented_by registerScopedEnvExtensionUnsafe]
opaque registerScopedEnvExtension (descr : Descr α β σ) : IO (ScopedEnvExtension α β σ)

/-- Get the extension idx for a ScopedEnvExtension -/
@[inline] private def getExtIdx (ext : ScopedEnvExtension α β σ) : Nat :=
  ext.ext.toEnvExtension.idx

def ScopedEnvExtension.pushScope (_ext : ScopedEnvExtension α β σ) (env : Environment) : Environment :=
  -- Per-extension pushScope uses centralized scope stack
  scopeStackExt.modifyState (asyncMode := .local) env fun sss =>
    let frame : ScopeFrame := {
      states := sss.currentStates
      activeScopes := sss.activeScopes
      delimitsLocal := sss.delimitsLocal
    }
    { sss with
      frames := frame :: sss.frames
      delimitsLocal := true }

unsafe def ScopedEnvExtension.popScopeUnsafe₁ (_ext : ScopedEnvExtension α β σ) (env : Environment) : Environment :=
  -- Per-extension popScope restores from centralized scope stack
  scopeStackExt.modifyState (asyncMode := .local) env fun sss =>
    match sss.frames with
    | frame :: rest =>
      { currentStates := frame.states
        activeScopes := frame.activeScopes
        delimitsLocal := frame.delimitsLocal
        frames := rest }
    | [] => sss

@[implemented_by ScopedEnvExtension.popScopeUnsafe₁]
opaque ScopedEnvExtension.popScope (ext : ScopedEnvExtension α β σ) (env : Environment) : Environment

/-- Modifies `delimitsLocal` flag to `false` to turn off delimiting of local entries.
-/
def ScopedEnvExtension.setDelimitsLocal (_ext : ScopedEnvExtension α β σ) (env : Environment) : Environment :=
  scopeStackExt.modifyState (asyncMode := .local) env fun sss =>
    { sss with delimitsLocal := false }

/-- Add a global entry: record in PersistentEnvExtension, then propagate to centralized
    current state and all saved scope frames. -/
unsafe def ScopedEnvExtension.addEntryUnsafe (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  -- 1. Record in PersistentEnvExtension (updates state, newEntries)
  let env := ext.ext.addEntry env (Entry.global b)
  -- 2. Propagate to centralized current state and all saved scope frames
  let idx := getExtIdx ext
  let sss := scopeStackExt.getState (asyncMode := .local) env
  -- Update current state
  let currentState : σ := match sss.currentStates.find? idx with
    | some s => ext.descr.addEntry (unsafeCast s) b
    | none =>
      match (ext.ext.getState (asyncMode := .local) env).stateStack with
      | st :: _ => ext.descr.addEntry st b
      | [] => unsafeCast ()
  let sss := { sss with currentStates := sss.currentStates.insert idx (unsafeCast currentState : EnvExtensionState) }
  -- Propagate to all saved scope frames
  let frames := sss.frames.map fun frame =>
    let frameState : σ := match frame.states.find? idx with
      | some s => ext.descr.addEntry (unsafeCast s) b
      | none =>
        match (ext.ext.getState (asyncMode := .local) env).stateStack with
        | st :: _ => ext.descr.addEntry st b
        | [] => unsafeCast ()
    { frame with states := frame.states.insert idx (unsafeCast frameState : EnvExtensionState) }
  scopeStackExt.modifyState (asyncMode := .local) env fun _ => { sss with frames }

@[implemented_by ScopedEnvExtension.addEntryUnsafe]
opaque ScopedEnvExtension.addEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment

/-- Add a scoped entry: record in PersistentEnvExtension, apply to centralized current state
    and saved frames where the namespace is active. -/
unsafe def ScopedEnvExtension.addScopedEntryUnsafe (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) (b : β) : Environment :=
  -- 1. Record in PersistentEnvExtension (updates scopedEntries, newEntries, and state if active)
  let env := ext.ext.addEntry env (Entry.«scoped» namespaceName b)
  -- 2. Apply to centralized current state and saved frames where namespace is active
  let sss := scopeStackExt.getState (asyncMode := .local) env
  let idx := getExtIdx ext
  -- Update current state if namespace is active
  let sss := if sss.activeScopes.contains namespaceName then
    let currentState : σ := match sss.currentStates.find? idx with
      | some s => ext.descr.addEntry (unsafeCast s) b
      | none =>
        match (ext.ext.getState (asyncMode := .local) env).stateStack with
        | st :: _ => ext.descr.addEntry st b
        | [] => unsafeCast ()
    { sss with currentStates := sss.currentStates.insert idx (unsafeCast currentState : EnvExtensionState) }
  else sss
  -- Propagate to saved frames where namespace is active
  let frames := sss.frames.map fun frame =>
    if frame.activeScopes.contains namespaceName then
      let frameState : σ := match frame.states.find? idx with
        | some s => ext.descr.addEntry (unsafeCast s) b
        | none => unsafeCast ()
      { frame with states := frame.states.insert idx (unsafeCast frameState : EnvExtensionState) }
    else
      frame
  scopeStackExt.modifyState (asyncMode := .local) env fun _ => { sss with frames }

@[implemented_by ScopedEnvExtension.addScopedEntryUnsafe]
opaque ScopedEnvExtension.addScopedEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) (b : β) : Environment

private unsafe def propagateLocalFrames (addEntry : EnvExtensionState → β → EnvExtensionState) (idx : Nat) (b : β)
    (frames : List ScopeFrame) (parentDelimits : Bool) : List ScopeFrame :=
  if parentDelimits then frames
  else match frames with
  | [] => []
  | frame :: rest =>
    let frameState := match frame.states.find? idx with
      | some s => addEntry s b
      | none => addEntry (unsafeCast ()) b
    let frame := { frame with states := frame.states.insert idx frameState }
    frame :: propagateLocalFrames addEntry idx b rest frame.delimitsLocal

/-- Propagate a local entry through the centralized scope stack.
    Local entries propagate to current state and through non-delimiting frames. -/
private unsafe def propagateLocalEntryUnsafe (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  let idx := getExtIdx ext
  let sss := scopeStackExt.getState (asyncMode := .local) env
  let addEntry : EnvExtensionState → β → EnvExtensionState :=
    fun s b => unsafeCast (ext.descr.addEntry (unsafeCast s : σ) b)
  -- Update current state
  let currentState : σ := match sss.currentStates.find? idx with
    | some s => ext.descr.addEntry (unsafeCast s) b
    | none =>
      match (ext.ext.getState (asyncMode := .local) env).stateStack with
      | st :: _ => ext.descr.addEntry st b
      | [] => unsafeCast ()
  let sss := { sss with currentStates := sss.currentStates.insert idx (unsafeCast currentState : EnvExtensionState) }
  -- Propagate through non-delimiting frames
  let frames := propagateLocalFrames addEntry idx b sss.frames sss.delimitsLocal
  scopeStackExt.modifyState (asyncMode := .local) env fun _ => { sss with frames }

@[implemented_by propagateLocalEntryUnsafe]
private opaque propagateLocalEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment

def ScopedEnvExtension.addLocalEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  propagateLocalEntry ext env b

def ScopedEnvExtension.addCore (env : Environment) (ext : ScopedEnvExtension α β σ) (b : β) (kind : AttributeKind) (namespaceName : Name) : Environment :=
  match kind with
  | AttributeKind.global => ext.addEntry env b
  | AttributeKind.local  => ext.addLocalEntry env b
  | AttributeKind.scoped => ext.addScopedEntry env namespaceName b

def ScopedEnvExtension.add [Monad m] [MonadResolveName m] [MonadEnv m] (ext : ScopedEnvExtension α β σ) (b : β) (kind := AttributeKind.global) : m Unit := do
  let ns ← getCurrNamespace
  modifyEnv (ext.addCore · b kind ns)

/-- Get the state of a scoped extension. Reads from centralized scope stack with fallback to
    PersistentEnvExtension state. -/
unsafe def ScopedEnvExtension.getStateUnsafe [Inhabited σ] (ext : ScopedEnvExtension α β σ)
    (env : Environment) (asyncMode := ext.ext.toEnvExtension.asyncMode) : σ :=
  let sss := scopeStackExt.getState (asyncMode := .local) env
  let idx := getExtIdx ext
  match sss.currentStates.find? idx with
  | some s => unsafeCast s
  | none =>
    -- Fallback to PersistentEnvExtension state
    match (ext.ext.getState (asyncMode := asyncMode) env).stateStack with
    | top :: _ => top
    | _        => unsafeCast ()

@[implemented_by ScopedEnvExtension.getStateUnsafe]
opaque ScopedEnvExtension.getState [Inhabited σ] (ext : ScopedEnvExtension α β σ)
    (env : Environment) (asyncMode := ext.ext.toEnvExtension.asyncMode) : σ

unsafe def ScopedEnvExtension.activateScopedUnsafe (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) : Environment :=
  let pstate := ext.ext.getState (asyncMode := .local) env
  -- Only update centralized state (scope-local, reverted by popScope)
  match pstate.scopedEntries.map.find? namespaceName with
  | none => env  -- No scoped entries for this namespace in this extension
  | some bs =>
    let idx := getExtIdx ext
    let sss := scopeStackExt.getState (asyncMode := .local) env
    let currentState : σ := match sss.currentStates.find? idx with
      | some s => unsafeCast s
      | none =>
        match pstate.stateStack with
        | st :: _ => st
        | [] => unsafeCast ()
    let state := Id.run do
      let mut state := currentState
      for b in bs do
        state := ext.descr.addEntry state b
      return state
    scopeStackExt.modifyState (asyncMode := .local) env fun sss =>
      { sss with
        currentStates := sss.currentStates.insert idx (unsafeCast state : EnvExtensionState) }

@[implemented_by ScopedEnvExtension.activateScopedUnsafe]
opaque ScopedEnvExtension.activateScoped (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) : Environment

unsafe def ScopedEnvExtension.modifyStateUnsafe (ext : ScopedEnvExtension α β σ) (env : Environment) (f : σ → σ) : Environment :=
  -- Only update centralized state. PersistentEnvExtension mirror is updated
  -- explicitly by addEntry/addScopedEntry when needed for olean export.
  let idx := getExtIdx ext
  let sss := scopeStackExt.getState (asyncMode := .local) env
  let currentState : σ := match sss.currentStates.find? idx with
    | some s => unsafeCast s
    | none =>
      match (ext.ext.getState (asyncMode := .local) env).stateStack with
      | top :: _ => top
      | _ => unsafeCast ()
  scopeStackExt.modifyState (asyncMode := .local) env fun sss =>
    { sss with currentStates := sss.currentStates.insert idx (unsafeCast (f currentState) : EnvExtensionState) }

@[implemented_by ScopedEnvExtension.modifyStateUnsafe]
opaque ScopedEnvExtension.modifyState (ext : ScopedEnvExtension α β σ) (env : Environment) (f : σ → σ) : Environment

/-- Centralized pushScope: snapshot all current states into a new frame. O(1). -/
def pushScope [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  modifyEnv fun env =>
    scopeStackExt.modifyState (asyncMode := .local) env fun sss =>
      let frame : ScopeFrame := {
        states := sss.currentStates
        activeScopes := sss.activeScopes
        delimitsLocal := sss.delimitsLocal
      }
      { sss with
        frames := frame :: sss.frames
        delimitsLocal := true }

/-- Centralized popScope: restore states from saved frame. O(1).
    Scoped entries are already propagated to saved frames by `addScopedEntry`,
    so no re-activation is needed. -/
unsafe def popScopeUnsafe [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  modifyEnv fun env =>
    scopeStackExt.modifyState (asyncMode := .local) env fun sss =>
      match sss.frames with
      | frame :: rest =>
        { currentStates := frame.states
          activeScopes := frame.activeScopes
          delimitsLocal := frame.delimitsLocal
          frames := rest }
      | [] => sss

@[implemented_by popScopeUnsafe]
opaque popScope [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit

/-- Used to implement `end_local_scope` command, that disables delimiting local entries of ScopedEnvExtension in a current scope.
-/
def setDelimitsLocal [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  modifyEnv fun env =>
    scopeStackExt.modifyState (asyncMode := .local) env fun sss =>
      { sss with delimitsLocal := false }

def activateScoped [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] (namespaceName : Name) : m Unit := do
  let env ← getEnv
  let sss := scopeStackExt.getState (asyncMode := .local) env
  if sss.activeScopes.contains namespaceName then return
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv (ext.activateScoped · namespaceName)
  modifyEnv fun env =>
    scopeStackExt.modifyState (asyncMode := .local) env fun sss =>
      { sss with activeScopes := sss.activeScopes.insert namespaceName }

/-- Initialize the centralized scope stack states from all registered scoped extensions.
    Called after finalizePersistentExtensions. -/
unsafe def initScopeStackStatesImpl (env : Environment) : IO Environment := do
  let exts ← scopedEnvExtensionsRef.get
  let mut currentStates : Lean.PersistentHashMap Nat EnvExtensionState := {}
  let mut activeScopes : NameSet := {}
  for scopedExt in exts do
    let idx := scopedExt.ext.toEnvExtension.idx
    let pstate := scopedExt.ext.getState (asyncMode := .local) env
    match pstate.stateStack with
    | st :: _ =>
      currentStates := currentStates.insert idx (unsafeCast st)
      activeScopes := activeScopes.merge pstate.activeScopes
    | [] => pure ()
  let sss : ScopeStackState := { currentStates, activeScopes }
  return scopeStackExt.modifyState (asyncMode := .local) env fun _ => sss

@[implemented_by initScopeStackStatesImpl]
opaque initScopeStackStates (env : Environment) : IO Environment

/-- Register the hook to initialize scope stack states after persistent extensions are finalized. -/
builtin_initialize
  postFinalizePersistentExtensionsHookRef.set initScopeStackStates

abbrev SimpleScopedEnvExtension (α : Type) (σ : Type) := ScopedEnvExtension α α σ

structure SimpleScopedEnvExtension.Descr (α : Type) (σ : Type) where
  name           : Name := by exact decl_name%
  addEntry       : σ → α → σ
  initial        : σ
  finalizeImport : σ → σ := id
  exportEntry?   : OLeanLevel → α → Option α := fun _ => some

def registerSimpleScopedEnvExtension (descr : SimpleScopedEnvExtension.Descr α σ) : IO (SimpleScopedEnvExtension α σ) := do
  registerScopedEnvExtension {
    name           := descr.name
    mkInitial      := return descr.initial
    addEntry       := descr.addEntry
    toOLeanEntry   := id
    ofOLeanEntry   := fun _ a => return a
    finalizeImport := descr.finalizeImport
    exportEntry?   := descr.exportEntry?
  }

end Lean
