/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Environment

public section

/-! Further environment extension API; the primitives live in `Lean.Environment`. -/

namespace Lean

/-- Simple `PersistentEnvExtension` that implements `exportEntriesFn` using a list of entries. -/
@[expose] def SimplePersistentEnvExtension (α σ : Type) := PersistentEnvExtension α α (List α × σ)

@[specialize] def mkStateFromImportedEntries {α σ : Type} (addEntryFn : σ → α → σ) (initState : σ) (as : Array (Array α)) : σ :=
  as.foldl (fun r es => es.foldl (fun r e => addEntryFn r e) r) initState

structure SimplePersistentEnvExtensionDescr (α σ : Type) where
  name          : Name := by exact decl_name%
  addEntryFn    : σ → α → σ
  addImportedFn : Array (Array α) → σ
  toArrayFn     : List α → Array α := fun es => es.toArray
  exportEntriesFnEx? :
    Option (Environment → σ → List α → OLeanLevel → Array α) := none
  asyncMode     : EnvExtension.AsyncMode := .mainOnly
  replay?       : Option ((newEntries : List α) → (newState : σ) → σ → List α × σ) := none

/--
Returns a function suitable for `SimplePersistentEnvExtensionDescr.replay?` that replays all new
entries onto the state using `addEntryFn`. `p` should filter out entries that have already been
added to the state by a prior replay of the same realizable constant.
-/
def SimplePersistentEnvExtension.replayOfFilter (p : σ → α → Bool)
    (addEntryFn : σ → α → σ) : List α → σ → σ → List α × σ :=
  fun newEntries _ s =>
    let newEntries := newEntries.filter (p s)
    (newEntries, newEntries.foldl (init := s) addEntryFn)

def registerSimplePersistentEnvExtension {α σ : Type} [Inhabited σ] (descr : SimplePersistentEnvExtensionDescr α σ) : IO (SimplePersistentEnvExtension α σ) :=
  registerPersistentEnvExtension {
    name            := descr.name,
    mkInitial       := pure ([], descr.addImportedFn #[]),
    addImportedFn   := fun as => pure ([], descr.addImportedFn as),
    addEntryFn      := fun s e => match s with
      | (entries, s) => (e::entries, descr.addEntryFn s e),
    exportEntriesFnEx env s level := match descr.exportEntriesFnEx? with
      | some fn => fn env s.2 s.1.reverse level
      | none    => descr.toArrayFn s.1.reverse
    statsFn := fun s => format "number of local entries: " ++ format s.1.length
    asyncMode := descr.asyncMode
    replay? := descr.replay?.map fun replay oldState newState _ (entries, s) =>
      let newEntries := newState.1.take (newState.1.length - oldState.1.length)
      let (newEntries, s) := replay newEntries newState.2 s
      (newEntries ++ entries, s)
  }

namespace SimplePersistentEnvExtension

instance {α σ : Type} [Inhabited σ] : Inhabited (SimplePersistentEnvExtension α σ) :=
  inferInstanceAs (Inhabited (PersistentEnvExtension α α (List α × σ)))

/-- Get the list of values used to update the state of the given
`SimplePersistentEnvExtension` in the current file. -/
def getEntries {α σ : Type} [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
    (env : Environment) (asyncMode := ext.toEnvExtension.asyncMode) : List α :=
  (PersistentEnvExtension.getState (asyncMode := asyncMode) ext env).1

/-- Get the current state of the given `SimplePersistentEnvExtension`. -/
def getState {α σ : Type} [Inhabited σ] (ext : SimplePersistentEnvExtension α σ) (env : Environment)
    (asyncMode := ext.toEnvExtension.asyncMode) (asyncDecl : Name := .anonymous) : σ :=
  (PersistentEnvExtension.getState (asyncMode := asyncMode) (asyncDecl := asyncDecl) ext env).2

/-- Set the current state of the given `SimplePersistentEnvExtension`. This change is *not* persisted across files. -/
def setState {α σ : Type} (ext : SimplePersistentEnvExtension α σ) (env : Environment) (s : σ) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun ⟨entries, _⟩ => (entries, s))

/-- Modify the state of the given extension in the given environment by applying the given function. This change is *not* persisted across files. -/
def modifyState {α σ : Type} (ext : SimplePersistentEnvExtension α σ) (env : Environment) (f : σ → σ) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun ⟨entries, s⟩ => (entries, f s))

end SimplePersistentEnvExtension

/-- Environment extension for tagging declarations.
    Declarations must only be tagged in the module where they were declared. -/
@[expose] def TagDeclarationExtension := SimplePersistentEnvExtension Name NameSet

def mkTagDeclarationExtension (name : Name := by exact decl_name%)
  (asyncMode : EnvExtension.AsyncMode := .mainOnly) : IO TagDeclarationExtension :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun _ => {},
    addEntryFn    := fun s n => s.insert n,
    toArrayFn     := fun es => es.toArray.qsort Name.quickLt
    asyncMode
  }

namespace TagDeclarationExtension

instance : Inhabited TagDeclarationExtension :=
  inferInstanceAs (Inhabited (SimplePersistentEnvExtension Name NameSet))

def tag (ext : TagDeclarationExtension) (env : Environment) (declName : Name) : Environment :=
  if declName.isAnonymous then
    -- This case might happen on partial elaboration; ignore instead of triggering any panics below
    env
  else
    have : Inhabited Environment := ⟨env⟩
    assert! env.getModuleIdxFor? declName |>.isNone -- See comment at `TagDeclarationExtension`
    ext.addEntry (asyncDecl := declName) env declName

def isTagged (ext : TagDeclarationExtension) (env : Environment) (declName : Name)
    (asyncMode := ext.toEnvExtension.asyncMode) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => (ext.getModuleEntries env modIdx).binSearchContains declName Name.quickLt
  | none        => (ext.getState (asyncMode := asyncMode) (asyncDecl := declName) env).contains declName

end TagDeclarationExtension

/-- Environment extension for mapping declarations to values.
    Declarations must only be inserted into the mapping in the module where they were declared. -/

structure MapDeclarationExtension (α : Type) extends PersistentEnvExtension (Name × α) (Name × α) (NameMap α)
deriving Inhabited

def mkMapDeclarationExtension (name : Name := by exact decl_name%)
    (asyncMode : EnvExtension.AsyncMode := .async .mainEnv)
    (exportEntriesFn : Environment → NameMap α → OLeanLevel → Array (Name × α) :=
      -- Do not export info for private defs by default
      fun env s _ => s.toArray.filter (fun (n, _) => env.contains (skipRealize := false) n)) :
    IO (MapDeclarationExtension α) :=
  .mk <$> registerPersistentEnvExtension {
    name            := name,
    mkInitial       := pure {}
    addImportedFn   := fun _ => pure {}
    addEntryFn      := fun s (n, v) => s.insert n v
    exportEntriesFnEx env s level := exportEntriesFn env s level
    asyncMode
    replay?         := some fun _ newState newConsts s =>
      newConsts.foldl (init := s) fun s c =>
        if let some a := newState.find? c then
          s.insert c a
        else s
  }

namespace MapDeclarationExtension

def insert (ext : MapDeclarationExtension α) (env : Environment) (declName : Name) (val : α) : Environment :=
  have : Inhabited Environment := ⟨env⟩
  if let some modIdx := env.getModuleIdxFor? declName then -- See comment at `MapDeclarationExtension`
    panic! s!"cannot insert `{declName}` into `{ext.name}`, it is not defined in the current module but in `{env.allImportedModuleNames[modIdx]!}`"
  else
    ext.addEntry (asyncDecl := declName) env (declName, val)

def find? [Inhabited α] (ext : MapDeclarationExtension α) (env : Environment) (declName : Name)
    (asyncMode := ext.toEnvExtension.asyncMode) (level := OLeanLevel.exported) : Option α :=
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    match (ext.getModuleEntries (level := level) env modIdx).binSearch (declName, default) (fun a b => Name.quickLt a.1 b.1) with
    | some e => some e.2
    | none   => none
  | none => (ext.getState (asyncMode := asyncMode) (asyncDecl := declName) env).find? declName

def contains [Inhabited α] (ext : MapDeclarationExtension α) (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => (ext.getModuleEntries env modIdx).binSearchContains (declName, default) (fun a b => Name.quickLt a.1 b.1)
  | none        => (ext.getState (asyncDecl := declName) env).contains declName

end MapDeclarationExtension
