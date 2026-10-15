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
  /--
  Whether this state may differ from the enclosing scope's state because of changes made since this
  scope was pushed: local entries, entries of namespaces activated in this scope, and
  `ScopedEnvExtension.modifyState`. Popping a scope with this flag set bumps the generation to a
  fresh value (see `PersistentEnvExtensionDescrCore.trackGen`) and, for an extension with
  `logWrites`, logs `scopeChangedDecls`. Only tracked for extensions with
  `Descr.tracksScopes`.
  -/
  scopeChanged : Bool := false
  /--
  The declarations of the entries added since this scope was pushed, which popping it removes again;
  collected only for extensions with `Descr.entryDecl?`.
  -/
  scopeChangedDecls : Array Name := #[]

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
  exportEntry?   : Environment → α → OLeanEntries (Option α) := fun _ a => .uniform (some a)
  /-- See `PersistentEnvExtensionDescrCore.trackGen`. -/
  trackGen : Bool := false
  /-- See `EnvExtension.logWrites`. -/
  logWrites : Bool := false
  /--
  The declaration an entry is about. Required with `logWrites`: adding an entry and scope
  operations adding or removing entries log their declarations (`Environment.logDeclChange`).
  -/
  entryDecl? : Option (β → Name) := none

/--
Whether scope operations that change the effective state must be recorded like content changes;
see `State.scopeChanged`.
-/
def Descr.tracksScopes (descr : Descr α β σ) : Bool :=
  descr.trackGen || descr.logWrites

/-- Notes on `s` that the entry `b` was added to it; see `State.scopeChanged`. -/
def Descr.noteScopeChange (descr : Descr α β σ) (s : State σ) (b : β) : State σ :=
  if descr.tracksScopes then
    { s with
      scopeChanged := true
      scopeChangedDecls := match descr.entryDecl? with
        | some decl => s.scopeChangedDecls.push (decl b)
        | none      => s.scopeChangedDecls }
  else
    s

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
            descr.noteScopeChange { s with state := descr.addEntry s.state b } b
          else
            s
      }

def exportEntriesFn (descr : Descr α β σ) (env : Environment) (s : StateStack α β σ) : OLeanEntries (Array (Entry α)) := Id.run do
  let mut exported : Array (Entry α) := #[]
  let mut server   : Array (Entry α) := #[]
  let mut priv     : Array (Entry α) := #[]
  for entry in s.newEntries.toArray.reverse do
    match entry with
    | .global e =>
      let r := descr.exportEntry? env e
      if let some e := r.exported then exported := exported.push (.global e)
      if let some e := r.server   then server   := server.push   (.global e)
      if let some e := r.private  then priv     := priv.push     (.global e)
    | .scoped ns e =>
      let r := descr.exportEntry? env e
      if let some e := r.exported then exported := exported.push (.scoped ns e)
      if let some e := r.server   then server   := server.push   (.scoped ns e)
      if let some e := r.private  then priv     := priv.push     (.scoped ns e)
  return { exported, server, «private» := priv }

end ScopedEnvExtension

open ScopedEnvExtension

structure ScopedEnvExtension (α : Type) (β : Type) (σ : Type) where
  descr : Descr α β σ
  ext   : PersistentEnvExtension (Entry α) (Entry β) (StateStack α β σ)
  deriving Inhabited

builtin_initialize scopedEnvExtensionsRef : IO.Ref (Array (ScopedEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)) ← IO.mkRef #[]

unsafe def registerScopedEnvExtensionUnsafe (descr : Descr α β σ) : IO (ScopedEnvExtension α β σ) := do
  if descr.logWrites && descr.entryDecl?.isNone then
    throw <| IO.userError s!"scoped environment extension `{descr.name}` with `logWrites` \
      must set `entryDecl?`"
  let ext ← registerPersistentEnvExtension {
    name            := descr.name
    mkInitial       := mkInitial descr
    addImportedFn   := addImportedFn descr
    addEntryFn      := addEntryFn descr
    exportEntriesFnEx := exportEntriesFn descr
    statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
    -- We restrict addition of global and `scoped` entries to the main thread but allow addition of
    -- scopes and local entries in any thread, which are visible only in that thread (see uses of
    -- `AsyncMode.local` below). Allowing the latter is important for tactics such as -- `classical`
    -- or `open in`.
    asyncMode       := .mainOnly
    trackGen        := descr.trackGen
    logWrites       := descr.logWrites
  }
  let ext := { descr := descr, ext := ext : ScopedEnvExtension α β σ }
  scopedEnvExtensionsRef.modify fun exts => exts.push (unsafeCast ext)
  return ext

@[implemented_by registerScopedEnvExtensionUnsafe]
opaque registerScopedEnvExtension (descr : Descr α β σ) : IO (ScopedEnvExtension α β σ)

/--
Applies a scope-stack operation `f`. `changed` must be set exactly when `f` changes the state in
effect (see `State.scopeChanged`), with `changedDecls` the declarations of the entries it adds or
removes. For extensions with `Descr.tracksScopes` this is recorded like a content change: the
generation of a generation-tracked extension is bumped, and one with `logWrites` logs
`changedDecls`.
-/
private def ScopedEnvExtension.modifyScopes (ext : ScopedEnvExtension α β σ) (env : Environment)
    (changed : Bool) (f : StateStack α β σ → StateStack α β σ) (changedDecls : Array Name := #[]) :
    Environment :=
  let record := changed && ext.descr.tracksScopes
  let env := if record && ext.descr.logWrites then
    changedDecls.foldl Environment.logDeclChange env
  else env
  -- unlogged: logged above if the state in effect changes
  ext.ext.modifyState (asyncMode := .local) (bumpGen := record) (log := .unlogged) env f

def ScopedEnvExtension.pushScope (ext : ScopedEnvExtension α β σ) (env : Environment) : Environment :=
  -- the new scope starts as a copy of the current state
  ext.modifyScopes env (changed := false) fun s =>
    match s.stateStack with
    | [] => s
    | state :: stack => { s with stateStack :=
      { state with delimitsLocal := true, scopeChanged := false, scopeChangedDecls := #[] } ::
        state :: stack }

def ScopedEnvExtension.popScope (ext : ScopedEnvExtension α β σ) (env : Environment) :
    Environment := Id.run do
  let top :: state₂ :: stack := (ext.ext.getState (asyncMode := .local) env).stateStack | return env
  ext.modifyScopes env (changed := top.scopeChanged) (changedDecls := top.scopeChangedDecls)
    fun s => { s with stateStack := state₂ :: stack }

/-- Modifies `delimitsLocal` flag to `false` on the top `depth` entries of the state stack,
to turn off delimiting of local entries across multiple implicit scope levels
(e.g. those introduced by compound `namespace A.B.C` expansions).
-/
def ScopedEnvExtension.setDelimitsLocal (ext : ScopedEnvExtension α β σ) (env : Environment) (depth : Nat) : Environment :=
  -- only affects where later local entries go
  ext.modifyScopes env (changed := false) fun s =>
    {s with stateStack := go depth s.stateStack}
where
  go : Nat → List (State σ) → List (State σ)
    | 0, stack => stack
    | _, [] => []
    | n + 1, state :: stack => {state with delimitsLocal := false} :: go n stack

/-- How to log a write of `b`. -/
@[inline] private def ScopedEnvExtension.writeLog (ext : ScopedEnvExtension α β σ) (b : β) :
    EnvExtension.WriteLog :=
  -- NOTE: `Descr.entryDecl?` is set whenever `logWrites` is, and without
  -- `logWrites` the named declaration is ignored.
  .decl (if let some decl := ext.descr.entryDecl? then decl b else .anonymous)

def ScopedEnvExtension.addEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  ext.ext.addEntry (log := ext.writeLog b) env (Entry.global b)

def ScopedEnvExtension.addScopedEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (namespaceName : Name) (b : β) : Environment :=
  ext.ext.addEntry (log := ext.writeLog b) env (Entry.«scoped» namespaceName b)

/-- The following function is used to implement `end_local_scope` command.

By default, all states have `delimitsLocal` set to `true`, and the following code modifies only the top element of the stack.
If the top element’s `delimitsLocal` is `false`, the function instead traverses down the stack until it reaches the first state where `delimitsLocal` is `true`.
Intuitively, `delimitsLocal` of each `State` determines whether local entries are delimited. When set to false, it allows traversal through implicit scopes where local entries are not delimited.
-/
def stateStackModify (ext : ScopedEnvExtension α β σ) (states : List (State σ)) (b : β) : List (State σ) :=
  match states with
  | [] => states
  | top :: states =>
    let top := ext.descr.noteScopeChange { top with state := ext.descr.addEntry top.state b } b
    let bot := if top.delimitsLocal then states else stateStackModify ext states b
    top :: bot

def ScopedEnvExtension.addLocalEntry (ext : ScopedEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  ext.ext.modifyState (asyncMode := .local) (log := ext.writeLog b) env fun s =>
    {s with stateStack := stateStackModify ext s.stateStack b}

def ScopedEnvExtension.addCore (env : Environment) (ext : ScopedEnvExtension α β σ) (b : β) (kind : AttributeKind) (namespaceName : Name) : Environment :=
  match kind with
  | AttributeKind.global => ext.addEntry env b
  | AttributeKind.local  => ext.addLocalEntry env b
  | AttributeKind.scoped => ext.addScopedEntry env namespaceName b

def ScopedEnvExtension.add [Monad m] [MonadResolveName m] [MonadEnv m] (ext : ScopedEnvExtension α β σ) (b : β) (kind := AttributeKind.global) : m Unit := do
  let ns ← getCurrNamespace
  modifyEnv (ext.addCore · b kind ns)

/-- Returns the state in effect. For `genRecorded`, see `EnvExtension.getState`. -/
def ScopedEnvExtension.getState [Inhabited σ] (ext : ScopedEnvExtension α β σ)
    (env : Environment) (asyncMode := ext.ext.toEnvExtension.asyncMode)
    (genRecorded := false) : σ :=
  match ext.ext.getState (asyncMode := asyncMode) (genRecorded := genRecorded) env |>.stateStack with
  | top :: _ => top.state
  | _        => unreachable!

def ScopedEnvExtension.activateScoped (ext : ScopedEnvExtension α β σ) (env : Environment)
    (namespaceName : Name) : Environment := Id.run do
  let s := ext.ext.getState (asyncMode := .local) env
  let top :: stack := s.stateStack | return env
  if top.activeScopes.contains namespaceName then
    return env
  let activeScopes := top.activeScopes.insert namespaceName
  let bs? := s.scopedEntries.map.find? namespaceName
  let top := if let some bs := bs? then
    bs.foldl (init := { top with activeScopes, delimitsLocal := true }) fun top b =>
      ext.descr.noteScopeChange { top with state := ext.descr.addEntry top.state b } b
  else
    { top with activeScopes }
  let decls := match bs?, ext.descr.entryDecl? with
    | some bs, some decl => bs.foldl (init := #[]) fun ds b => ds.push (decl b)
    | _, _ => #[]
  ext.modifyScopes env (changed := bs?.isSome) (changedDecls := decls) fun s =>
    { s with stateStack := top :: stack }

def ScopedEnvExtension.modifyState (ext : ScopedEnvExtension α β σ) (env : Environment) (f : σ → σ) : Environment :=
  ext.ext.modifyState env fun s =>
    match s.stateStack with
    | top :: stack =>
      let scopeChanged := top.scopeChanged || ext.descr.tracksScopes
      { s with stateStack := { top with state := f top.state, scopeChanged } :: stack }
    | _ => s

def pushScope [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv ext.pushScope

def popScope [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv ext.popScope

/-- Used to implement `end_local_scope` command, that disables delimiting local entries of ScopedEnvExtension
across `depth` scope levels.
-/
def setDelimitsLocal [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] (depth : Nat) : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv (ext.setDelimitsLocal · depth)

def activateScoped [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] (namespaceName : Name) : m Unit := do
  for ext in (← scopedEnvExtensionsRef.get) do
    modifyEnv (ext.activateScoped · namespaceName)

abbrev SimpleScopedEnvExtension (α : Type) (σ : Type) := ScopedEnvExtension α α σ

structure SimpleScopedEnvExtension.Descr (α : Type) (σ : Type) where
  name           : Name := by exact decl_name%
  addEntry       : σ → α → σ
  initial        : σ
  finalizeImport : σ → σ := id
  exportEntry?   : Environment → α → OLeanEntries (Option α) := fun _ a => .uniform (some a)
  /-- See `PersistentEnvExtensionDescrCore.trackGen`. -/
  trackGen : Bool := false
  /-- See `EnvExtension.logWrites`. -/
  logWrites : Bool := false
  /-- See `ScopedEnvExtension.Descr.entryDecl?`. -/
  entryDecl? : Option (α → Name) := none

def registerSimpleScopedEnvExtension (descr : SimpleScopedEnvExtension.Descr α σ) : IO (SimpleScopedEnvExtension α σ) := do
  registerScopedEnvExtension {
    name           := descr.name
    mkInitial      := return descr.initial
    addEntry       := descr.addEntry
    toOLeanEntry   := id
    ofOLeanEntry   := fun _ a => return a
    finalizeImport := descr.finalizeImport
    exportEntry?   := descr.exportEntry?
    trackGen       := descr.trackGen
    logWrites      := descr.logWrites
    entryDecl?     := descr.entryDecl?
  }

end Lean
