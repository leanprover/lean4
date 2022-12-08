/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.Data.NameTrie
import Lean.Attributes

namespace Lean

namespace ScopedEnvExtension

inductive Entry (α : Type) where
  | global : α → Entry α
  | scoped : Name → α → Entry α

structure State (σ : Type) where
  state        : σ
  activeScopes : NameSet := {}

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

def exportEntriesFn (s : StateStack α β σ) : Array (Entry α) :=
  s.newEntries.toArray.reverse

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
    exportEntriesFn := exportEntriesFn
    statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
  }
  let ext := { descr := descr, ext := ext : ScopedEnvExtension α β σ }
  scopedEnvExtensionsRef.modify fun exts => exts.push (unsafeCast ext)
  return ext

@[implemented_by registerScopedEnvExtensionUnsafe]
opaque registerScopedEnvExtension (descr : Descr α β σ) : IO (ScopedEnvExtension α β σ)

def ScopedEnvExtension.pushScope (ext : ScopedEnvExtension α β σ) (env : Environment) : Environment :=
  let s := ext.ext.getState env
  match s.stateStack with
  | [] => env
  | state :: stack => ext.ext.setState env { s with stateStack := state :: state :: stack }

def ScopedEnvExtension.popScope (ext : ScopedEnvExtension α β σ) (env : Environment) : Environment :=
  let s := ext.ext.getState env
  match s.stateStack with
  | _      :: state₂ :: stack => ext.ext.setState env { s with stateStack := state₂ :: stack }
  | _ => env

def ScopedEnvExtension.addEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  ext.ext.addEntry env (Entry.global b)

def ScopedEnvExtension.addScopedEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) (b : β) : Environment :=
  ext.ext.addEntry env (Entry.«scoped» namespaceName b)

def ScopedEnvExtension.addLocalEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  let s := ext.ext.getState env
  match s.stateStack with
  | [] => env
  | top :: states =>
    let top := { top with state := ext.descr.addEntry top.state b }
    ext.ext.setState env { s with stateStack := top :: states }

def ScopedEnvExtension.add [Monad m] [MonadResolveName m] [MonadEnv m] (ext : ScopedEnvExtension α β σ) (b : β) (kind := AttributeKind.global) : m Unit := do
  match kind with
  | AttributeKind.global => modifyEnv (ext.addEntry · b)
  | AttributeKind.local  => modifyEnv (ext.addLocalEntry · b)
  | AttributeKind.scoped => modifyEnv (ext.addScopedEntry · (← getCurrNamespace) b)

def ScopedEnvExtension.getState [Inhabited σ] (ext : ScopedEnvExtension α β σ) (env : Environment) : σ :=
  match ext.ext.getState env |>.stateStack with
  | top :: _ => top.state
  | _        => unreachable!

def ScopedEnvExtension.activateScoped (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) : Environment :=
  let s := ext.ext.getState env
  match s.stateStack with
  | top :: stack =>
    if top.activeScopes.contains namespaceName then
      env
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
      ext.ext.setState env { s with stateStack := top :: stack }
  | _ => env

def ScopedEnvExtension.modifyState (ext : ScopedEnvExtension α β σ) (env : Environment) (f : σ → σ) : Environment :=
  let s := ext.ext.getState env
  match s.stateStack with
  | top :: stack => ext.ext.setState env { s with stateStack := { top with state := f top.state } :: stack }
  | _ => env

def pushScope [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv ext.pushScope

def popScope [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv ext.popScope

def activateScoped [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] (namespaceName : Name) : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv (ext.activateScoped · namespaceName)

abbrev SimpleScopedEnvExtension (α : Type) (σ : Type) := ScopedEnvExtension α α σ

structure SimpleScopedEnvExtension.Descr (α : Type) (σ : Type) where
  name           : Name := by exact decl_name%
  addEntry       : σ → α → σ
  initial        : σ
  finalizeImport : σ → σ := id

def registerSimpleScopedEnvExtension (descr : SimpleScopedEnvExtension.Descr α σ) : IO (SimpleScopedEnvExtension α σ) := do
  registerScopedEnvExtension {
    name           := descr.name
    mkInitial      := return descr.initial
    addEntry       := descr.addEntry
    toOLeanEntry   := id
    ofOLeanEntry   := fun _ a => return a
    finalizeImport := descr.finalizeImport
  }

end Lean
