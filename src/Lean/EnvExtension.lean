/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Environment
import Init.Data.UInt.Lemmas

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
    Option (Environment → σ → List α → OLeanEntries (Array α)) := none
  asyncMode     : EnvExtension.AsyncMode := .mainOnly
  replay?       : Option ((newEntries : List α) → (newState : σ) → σ → List α × σ) := none
  /-- See `EnvExtension.logWrites`. -/
  logWrites     : Bool := false

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
    exportEntriesFnEx env s := match descr.exportEntriesFnEx? with
      | some fn => fn env s.2 s.1.reverse
      | none    => .uniform (descr.toArrayFn s.1.reverse)
    statsFn := fun s => format "number of local entries: " ++ format s.1.length
    asyncMode := descr.asyncMode
    logWrites := descr.logWrites
    replay? := descr.replay?.map fun replay oldState newState _ (entries, s) =>
      let newEntries := takeNewEntries newState.1 oldState.1
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

/--
`entries.binSearch (declName, default) (fun a b => Name.quickLt a.1 b.1)` with the same probes, but
comparing the names directly: one `Name.quickCmp` per probe instead of up to two calls of a closure.
The USize cutoff keeps `lo + hi` below `USize.size`, including on 32-bit platforms.
-/
def findSortedByName? (entries : Array (Name × α)) (declName : Name) : Option (Name × α) :=
  if h : 0 < entries.size then
    if hs : entries.size < 2147483647 then
      goUSize hs 0 (USize.ofNat32 (entries.size - 1) (by omega)) (by simp) (by simp; omega)
    else
      go 0 (entries.size - 1) (by omega) (by omega)
  else none
where
  goUSize (hsize : entries.size < 2147483647) (lo hi : USize)
      (hlo : lo.toNat ≤ hi.toNat) (hhi : hi.toNat < entries.size) : Option (Name × α) :=
    let m := (lo + hi) / 2
    have hs : 4294967296 ≤ 2 ^ System.Platform.numBits := USize.le_size
    have htwo : (2 : USize).toNat = 2 := by simp
    have hm : m.toNat = (lo.toNat + hi.toNat) / 2 := by
      simp only [m, USize.toNat_div, USize.toNat_add, htwo]
      rw [Nat.mod_eq_of_lt (by omega)]
    have hnext : (m + 1).toNat = m.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]
    let e := entries.uget m (by omega)
    match Name.quickCmp e.1 declName with
    | .lt => if h : m + 1 ≤ hi then goUSize hsize (m + 1) hi h hhi else none
    | .gt =>
      if h : lo < m then
        have hlt : lo.toNat < m.toNat := h
        have hp : (m - 1).toNat = m.toNat - 1 := by
          rw [USize.toNat_sub_of_le _ _ (by
            simp only [USize.le_iff_toNat_le, USize.toNat_one]
            omega), USize.toNat_one]
        goUSize hsize lo (m - 1) (by omega) (by omega)
      else none
    | .eq => some e
  termination_by hi.toNat + 1 - lo.toNat
  decreasing_by
    · rw [hnext]
      have : (m + 1).toNat ≤ hi.toNat := h
      omega
    · rw [hp]
      omega

  go (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi < entries.size) : Option (Name × α) :=
    let m := (lo + hi) / 2
    let e := entries[m]'(by omega)
    match Name.quickCmp e.1 declName with
    | .lt => if h : m + 1 ≤ hi then go (m + 1) hi h hhi else none
    | .gt => if h : m = 0 ∨ m - 1 < lo then none else go lo (m - 1) (by omega) (by omega)
    | .eq => some e
  termination_by hi + 1 - lo

/-- `entries.find? (·.1 == declName)`, without calling a closure on each entry. -/
def findByName? (entries : Array (Name × α)) (declName : Name) : Option (Name × α) :=
  go 0
where
  go (i : Nat) : Option (Name × α) :=
    if h : i < entries.size then
      let e := entries[i]
      if e.1 == declName then some e else go (i + 1)
    else
      none
  termination_by entries.size - i

/-- `names.binSearchContains declName Name.quickLt`, comparing as `findSortedByName?` does. -/
def containsSortedName (names : Array Name) (declName : Name) : Bool :=
  if h : 0 < names.size then
    if hs : names.size < 2147483647 then
      goUSize hs 0 (USize.ofNat32 (names.size - 1) (by omega)) (by simp) (by simp; omega)
    else
      go 0 (names.size - 1) (by omega) (by omega)
  else false
where
  goUSize (hsize : names.size < 2147483647) (lo hi : USize)
      (hlo : lo.toNat ≤ hi.toNat) (hhi : hi.toNat < names.size) : Bool :=
    let m := (lo + hi) / 2
    have hs : 4294967296 ≤ 2 ^ System.Platform.numBits := USize.le_size
    have htwo : (2 : USize).toNat = 2 := by simp
    have hm : m.toNat = (lo.toNat + hi.toNat) / 2 := by
      simp only [m, USize.toNat_div, USize.toNat_add, htwo]
      rw [Nat.mod_eq_of_lt (by omega)]
    have hnext : (m + 1).toNat = m.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]
    match Name.quickCmp (names.uget m (by omega)) declName with
    | .lt => if h : m + 1 ≤ hi then goUSize hsize (m + 1) hi h hhi else false
    | .gt =>
      if h : lo < m then
        have hlt : lo.toNat < m.toNat := h
        have hp : (m - 1).toNat = m.toNat - 1 := by
          rw [USize.toNat_sub_of_le _ _ (by
            simp only [USize.le_iff_toNat_le, USize.toNat_one]
            omega), USize.toNat_one]
        goUSize hsize lo (m - 1) (by omega) (by omega)
      else false
    | .eq => true
  termination_by hi.toNat + 1 - lo.toNat
  decreasing_by
    · rw [hnext]
      have : (m + 1).toNat ≤ hi.toNat := h
      omega
    · rw [hp]
      omega

  go (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi < names.size) : Bool :=
    let m := (lo + hi) / 2
    match Name.quickCmp (names[m]'(by omega)) declName with
    | .lt => if h : m + 1 ≤ hi then go (m + 1) hi h hhi else false
    | .gt => if h : m = 0 ∨ m - 1 < lo then false else go lo (m - 1) (by omega) (by omega)
    | .eq => true
  termination_by hi + 1 - lo

/-- Environment extension for tagging declarations.
    Declarations must only be tagged in the module where they were declared. -/
@[expose] def TagDeclarationExtension := SimplePersistentEnvExtension Name NameSet

def mkTagDeclarationExtension (name : Name := by exact decl_name%)
  (asyncMode : EnvExtension.AsyncMode := .mainOnly)
  (logWrites : Bool := false) : IO TagDeclarationExtension :=
  registerSimplePersistentEnvExtension {
    name          := name,
    logWrites     := logWrites,
    addImportedFn := fun _ => {},
    addEntryFn    := fun s n => s.insert n,
    toArrayFn     := fun es => es.toArray.qsort Name.quickLt
    asyncMode
    replay?       := some <|
      SimplePersistentEnvExtension.replayOfFilter (!·.contains ·) (·.insert ·)
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
    -- Only the state visible on this branch, as in `MapDeclarationExtension.insert`: a tag added on
    -- the still-running branch of `declName` is missed, which only costs a superfluous log entry.
    if ext.getState (asyncMode := .local) env |>.contains declName then
      env
    else
      ext.addEntry (asyncDecl := declName) (log := .decl declName) env declName

def isTagged (ext : TagDeclarationExtension) (env : Environment) (declName : Name)
    (asyncMode := ext.toEnvExtension.asyncMode) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => containsSortedName (ext.getModuleEntries env modIdx) declName
  | none        => (ext.getState (asyncMode := asyncMode) (asyncDecl := declName) env).contains declName

end TagDeclarationExtension

/-- Environment extension for mapping declarations to values.
    Declarations must only be inserted into the mapping in the module where they were declared. -/

structure MapDeclarationExtension (α : Type) extends PersistentEnvExtension (Name × α) (Name × α) (NameMap α)
deriving Inhabited

def mkMapDeclarationExtension (name : Name := by exact decl_name%)
    (asyncMode : EnvExtension.AsyncMode := .async .mainEnv)
    (logWrites : Bool := false)
    (exportEntriesFn : Environment → NameMap α → OLeanEntries (Array (Name × α)) :=
      fun env s =>
        let all := s.toArray.filter (fun (n, _) => env.contains (skipRealize := false) n)
        -- Do not export info for private defs by default
        let exported := all.filter fun (n, _) =>
          (env.setExporting true).contains (skipRealize := false) n
        { exported, server := exported, «private» := all }) :
    IO (MapDeclarationExtension α) :=
  .mk <$> registerPersistentEnvExtension {
    name            := name,
    logWrites       := logWrites,
    mkInitial       := pure {}
    addImportedFn   := fun _ => pure {}
    addEntryFn      := fun s (n, v) => s.insert n v
    exportEntriesFnEx env s := exportEntriesFn env s
    asyncMode
    replay?         := some fun _ newState newConsts s =>
      newConsts.foldl (init := s) fun s c =>
        if let some a := newState.find? c then
          s.insert c a
        else s
  }

namespace MapDeclarationExtension

/--
Adds the entry for `declName`. Entries are write-once: facts derived from an entry, such as cached
type class resolution results, assume it never changes. `allowOverwrite` permits replacing an
existing entry, which invalidates such facts; use it only where that is justified, and say why.
-/
def insert (ext : MapDeclarationExtension α) (env : Environment) (declName : Name) (val : α)
    (allowOverwrite := false) : Environment :=
  have : Inhabited Environment := ⟨env⟩
  if let some modIdx := env.getModuleIdxFor? declName then -- See comment at `MapDeclarationExtension`
    panic! s!"cannot insert `{declName}` into `{ext.name}`, it is not defined in the current module but in `{env.allImportedModuleNames[modIdx]!}`"
  -- Check only the state visible on this branch: writes often happen here while the branch
  -- elaborating `declName` (e.g. a theorem's proof) still runs, and waiting for it would stall the
  -- write. This still catches every double write whose first write is visible here, in particular
  -- all sequential ones; it misses only a first write made on that still-running branch.
  else if !allowOverwrite &&
      (ext.toPersistentEnvExtension.getState (asyncMode := .local) env).contains declName then
    panic! s!"cannot insert `{declName}` into `{ext.name}`, it is already present; \
      declaration-keyed extension entries are write-once (pass `allowOverwrite := true` if this \
      update is intended)"
  else
    ext.addEntry (asyncDecl := declName) (log := .decl declName) env (declName, val)

def find? [Inhabited α] (ext : MapDeclarationExtension α) (env : Environment) (declName : Name)
    (asyncMode := ext.toEnvExtension.asyncMode) (level := OLeanLevel.exported) : Option α :=
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    match findSortedByName? (ext.getModuleEntries (level := level) env modIdx) declName with
    | some e => some e.2
    | none   => none
  | none => (ext.getState (asyncMode := asyncMode) (asyncDecl := declName) env).find? declName

def contains [Inhabited α] (ext : MapDeclarationExtension α) (env : Environment) (declName : Name)
    (asyncMode := ext.toEnvExtension.asyncMode) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => (findSortedByName? (ext.getModuleEntries env modIdx) declName).isSome
  | none        => (ext.getState (asyncMode := asyncMode) (asyncDecl := declName) env).contains declName

end MapDeclarationExtension
