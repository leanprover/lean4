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

structure State (σ : Type) where
  state        : σ
  activeScopes : NameSet := {}
  delimitsLocal : Bool := true -- used for implementing `end_local_scope`.

structure ScopedEntries (β : Type) where
  map : SMap Name (PArray β) := {}
  deriving Inhabited
structure StateStack (α : Type) (β : Type) (σ : Type) where
  stateStack    : List (State σ) := {}
  scopedEntries : ScopedEntries β := {}
  newEntries    : List (Entry α) := []
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
  return { stateStack := [ { state := (← descr.mkInitial ) } ] }

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
  return { stateStack := [ { state := s } ], scopedEntries := scopedEntries }

def addEntryFn (descr : Descr α β σ) (s : StateStack α β σ) (e : Entry β) : StateStack α β σ :=
  match s with
  | { stateStack := stateStack, scopedEntries := scopedEntries, newEntries := newEntries } =>
    match e with
    | Entry.global b => {
        scopedEntries := scopedEntries
        newEntries    := (Entry.global (descr.toOLeanEntry b)) :: newEntries
        stateStack    := stateStack.map fun s => { s with state := descr.addEntry s.state b }
      }
    | Entry.«scoped» ns b =>
      {
        scopedEntries := scopedEntries.insert ns b
        newEntries    := (Entry.«scoped» ns (descr.toOLeanEntry b)) :: newEntries
        stateStack    := stateStack.map fun s =>
          if s.activeScopes.contains ns then
            { s with state := descr.addEntry s.state b }
          else
            s
      }

def exportEntriesFn (descr : Descr α β σ) (level : OLeanLevel) (s : StateStack α β σ) : Array (Entry α) :=
  s.newEntries.toArray.reverse.filterMap fun
    | .global e => .global <$> descr.exportEntry? level e
    | .scoped ns e => .scoped ns <$> descr.exportEntry? level e

end ScopedEnvExtension

open ScopedEnvExtension

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

def ScopedEnvExtension.pushScope (ext : ScopedEnvExtension α β σ) (env : Environment) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    match s.stateStack with
    | [] => s
    | state :: stack => { s with stateStack := { state with delimitsLocal := true } :: state :: stack }

def ScopedEnvExtension.popScope (ext : ScopedEnvExtension α β σ) (env : Environment) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    match s.stateStack with
    | _      :: state₂ :: stack => { s with stateStack := state₂ :: stack }
    | _ => s

/-- Modifies `delimitsLocal` flag to `false` to turn off delimiting of local entries.
-/
def ScopedEnvExtension.setDelimitsLocal (ext : ScopedEnvExtension α β σ) (env : Environment)  : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    match s.stateStack with
    | [] => s
    | state :: stack => {s with stateStack := {state with delimitsLocal := false} :: stack}

def ScopedEnvExtension.addEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  ext.ext.addEntry env (Entry.global b)

def ScopedEnvExtension.addScopedEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) (b : β) : Environment :=
  ext.ext.addEntry env (Entry.«scoped» namespaceName b)

/-- The following function is used to implement `end_local_scope` command.

By default, all states have `delimitsLocal` set to `true`, and the following code modifies only the top element of the stack.
If the top element’s `delimitsLocal` is `false`, the function instead traverses down the stack until it reaches the first state where `delimitsLocal` is `true`.
Intuitively, `delimitsLocal` of each `State` determines whether local entries are delimited. When set to false, it allows traversal through implicit scopes where local entries are not delimited.
-/
def stateStackModify (ext : ScopedEnvExtension α β σ) (states : List (State σ)) (b : β) : List (State σ) :=
  match states with
  | [] => states
  | top :: states =>
    let top := { top with state := ext.descr.addEntry top.state b }
    let bot := if top.delimitsLocal then states else stateStackModify ext states b
    top :: bot

def ScopedEnvExtension.addLocalEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    {s with stateStack := stateStackModify ext s.stateStack b}

def ScopedEnvExtension.addCore (env : Environment) (ext : ScopedEnvExtension α β σ) (b : β) (kind : AttributeKind) (namespaceName : Name) : Environment :=
  match kind with
  | AttributeKind.global => ext.addEntry env b
  | AttributeKind.local  => ext.addLocalEntry env b
  | AttributeKind.scoped => ext.addScopedEntry env namespaceName b

def ScopedEnvExtension.add [Monad m] [MonadResolveName m] [MonadEnv m] (ext : ScopedEnvExtension α β σ) (b : β) (kind := AttributeKind.global) : m Unit := do
  let ns ← getCurrNamespace
  modifyEnv (ext.addCore · b kind ns)

def ScopedEnvExtension.getState [Inhabited σ] (ext : ScopedEnvExtension α β σ)
    (env : Environment) (asyncMode := ext.ext.toEnvExtension.asyncMode) : σ :=
  match ext.ext.getState (asyncMode := asyncMode) env |>.stateStack with
  | top :: _ => top.state
  | _        => unreachable!

def ScopedEnvExtension.activateScoped (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    match s.stateStack with
    | top :: stack =>
      if top.activeScopes.contains namespaceName then
        s
      else
        let activeScopes := top.activeScopes.insert namespaceName
        let top :=
          match s.scopedEntries.map.find? namespaceName with
          | none =>
            { top with activeScopes := activeScopes }
          | some bs => Id.run do
            let mut state := top.state
            for b in bs do
              state := ext.descr.addEntry state b
            { state := state, activeScopes := activeScopes }
        { s with stateStack := top :: stack }
    | _ => s

def ScopedEnvExtension.modifyState (ext : ScopedEnvExtension α β σ) (env : Environment) (f : σ → σ) : Environment :=
  ext.ext.modifyState env fun s =>
    match s.stateStack with
    | top :: stack => { s with stateStack := { top with state := f top.state } :: stack }
    | _ => s

def pushScope [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv ext.pushScope

def popScope [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv ext.popScope

/-- Used to implement `end_local_scope` command, that disables delimiting local entries of ScopedEnvExtension in a current scope.
-/
def setDelimitsLocal [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv (ext.setDelimitsLocal ·)

def activateScoped [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] (namespaceName : Name) : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv (ext.activateScoped · namespaceName)

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
