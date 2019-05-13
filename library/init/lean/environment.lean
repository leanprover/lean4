/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.io
import init.util
import init.data.bytearray
import init.lean.declaration
import init.lean.smap

namespace Lean
/- Opaque environment extension state. It is essentially the Lean version of a C `void *`
   TODO: mark opaque -/
@[derive Inhabited]
def EnvExtensionState : Type := NonScalar

/- TODO: mark opaque. -/
@[derive Inhabited]
def ModuleId := Nat

/- TODO: mark opaque. -/
structure Environment :=
(const2ModId : HashMap Name ModuleId)
(constants   : SMap Name ConstantInfo Name.quickLt)
(extensions  : Array EnvExtensionState)
(trustLevel  : UInt32     := 0)
(quotInit    : Bool       := false)
(imports     : Array Name := Array.empty)

namespace Environment

instance : Inhabited Environment :=
⟨{ const2ModId := {}, constants := {}, extensions := Array.empty }⟩

@[export lean.environment_add_core]
def add (env : Environment) (cinfo : ConstantInfo) : Environment :=
{ constants := env.constants.insert cinfo.name cinfo, .. env }

@[export lean.environment_find_core]
def find (env : Environment) (n : Name) : Option ConstantInfo :=
env.constants.find n

def contains (env : Environment) (n : Name) : Bool :=
(env.constants.find n).isSome

/- Switch environment to "shared" mode. -/
@[export lean.environment_switch_core]
private def switch (env : Environment) : Environment :=
{ constants := env.constants.switch, .. env }

@[export lean.environment_mark_quot_init_core]
private def markQuotInit (env : Environment) : Environment :=
{ quotInit := true, .. env }

@[export lean.environment_quot_init_core]
private def isQuotInit (env : Environment) : Bool :=
env.quotInit

@[export lean.environment_trust_level_core]
private def getTrustLevel (env : Environment) : UInt32 :=
env.trustLevel

end Environment

/- "Raw" environment extension.
   TODO: mark opaque. -/
structure EnvExtension (σ : Type) :=
(idx       : Nat)
(initial   : σ)

namespace EnvExtension

unsafe def setStateUnsafe {σ : Type} (ext : EnvExtension σ) (env : Environment) (s : σ) : Environment :=
{ extensions := env.extensions.set ext.idx (unsafeCast s), .. env }

@[implementedBy setStateUnsafe]
constant setState {σ : Type} (ext : EnvExtension σ) (env : Environment) (s : σ) : Environment := default _

unsafe def getStateUnsafe {σ : Type} (ext : EnvExtension σ) (env : Environment) : σ :=
let s : EnvExtensionState := env.extensions.get ext.idx in
@unsafeCast _ _ ⟨ext.initial⟩ s

@[implementedBy getStateUnsafe]
constant getState {σ : Type} (ext : EnvExtension σ) (env : Environment) : σ := ext.initial

@[inline] unsafe def modifyStateUnsafe {σ : Type} (ext : EnvExtension σ) (env : Environment) (f : σ → σ) : Environment :=
{ extensions := env.extensions.modify ext.idx $ λ s,
    let s : σ := (@unsafeCast _ _ ⟨ext.initial⟩ s) in
    let s : σ := f s in
    unsafeCast s,
  .. env }

@[implementedBy modifyStateUnsafe]
constant modifyState {σ : Type} (ext : EnvExtension σ) (env : Environment) (f : σ → σ) : Environment := default _

end EnvExtension

private def mkEnvExtensionsRef : IO (IO.Ref (Array (EnvExtension EnvExtensionState))) :=
IO.mkRef Array.empty

@[init mkEnvExtensionsRef]
private constant envExtensionsRef : IO.Ref (Array (EnvExtension EnvExtensionState)) := default _

instance EnvExtension.Inhabited (σ : Type) [Inhabited σ] : Inhabited (EnvExtension σ) :=
⟨{ idx := 0, initial := default _ }⟩

unsafe def registerEnvExtensionUnsafe {σ : Type} (initState : σ) : IO (EnvExtension σ) :=
do
initializing ← IO.initializing,
unless initializing $ throw (IO.userError ("Failed to register environment, extensions can only be registered during initialization")),
exts ← envExtensionsRef.get,
let idx := exts.size,
let ext : EnvExtension σ := {
   idx     := idx,
   initial := initState
},
envExtensionsRef.modify (λ exts, exts.push (unsafeCast ext)),
pure ext

/- Environment extensions can only be registered during initialization.
   Reasons:
   1- Our implementation assumes the number of extensions does not change after an environment object is created.
   2- We do not use any synchronization primitive to access `envExtensionsRef`. -/
@[implementedBy registerEnvExtensionUnsafe]
constant registerEnvExtension {σ : Type} (initState : σ) : IO (EnvExtension σ) := default _

@[export lean.mk_empty_environment_core]
def mkEmptyEnvironment (trustLevel : UInt32 := 0) : IO Environment :=
do
initializing ← IO.initializing,
when initializing $ throw (IO.userError "Environment objects cannot be created during initialization"),
exts ← envExtensionsRef.get,
pure { const2ModId := {},
       constants   := {},
       trustLevel  := trustLevel,
       extensions  := exts.map $ λ ext, ext.initial }

structure PersistentEnvExtensionState (α : Type) (σ : Type) :=
(importedEntries : Array (Array α))  -- entries per imported module
(importedState   : Thunk σ)          -- state after processing all entries in `importedEntries`
(entries         : List α   := [])   -- entries defined in the current module
(state           : Option σ := none) -- state after processing `importedEntries` and `entries`

/- An environment extension with support for storing/retrieving entries from a .olean file.
   - α is the entry type.
   - σ is the actual state.
   We re-construct the actual state lazily. Moreover, if function `PersistentEnvExtension.getState` is not
   used, then we don't even compute the field `state`.

   TODO: mark opaque. -/
structure PersistentEnvExtension (α : Type) (σ : Type) extends EnvExtension (PersistentEnvExtensionState α σ) :=
(name       : Name)
(someVal    : α)
(addEntryFn : Bool → σ → α → σ)
(toArrayFn  : List α → Array α)

/- Opaque persistent environment extension entry. It is essentially a C `void *`
   TODO: mark opaque -/
@[derive Inhabited]
def EnvExtensionEntry := NonScalar

instance PersistentEnvExtensionState.inhabited : Inhabited (PersistentEnvExtensionState EnvExtensionEntry EnvExtensionState) :=
⟨{importedEntries := Array.empty, importedState := Thunk.pure (default _) }⟩

instance PersistentEnvExtension.inhabited : Inhabited (PersistentEnvExtension EnvExtensionEntry EnvExtensionState) :=
⟨{ toEnvExtension := { idx := 0, initial := default _ },
   name := default _, someVal := default _, addEntryFn := λ _ s _, s, toArrayFn := λ es, es.toArray }⟩

namespace PersistentEnvExtension

def getEntries {α σ : Type} (ext : PersistentEnvExtension α σ) (env : Environment) : List α :=
(ext.toEnvExtension.getState env).entries

def getModuleEntries {α σ : Type} (ext : PersistentEnvExtension α σ) (env : Environment) (m : ModuleId) : Array α :=
(ext.toEnvExtension.getState env).importedEntries.get m

def addEntry {α σ : Type} (ext : PersistentEnvExtension α σ) (env : Environment) (a : α) : Environment :=
ext.toEnvExtension.modifyState env $ λ s,
  let entries := a :: s.entries in
  match s.state with
  | none   := { entries := entries, .. s }
  | some d := { entries := entries, state := some (ext.addEntryFn false d a), .. s }

def forceStateAux {α σ : Type} (ext : PersistentEnvExtension α σ) (s : PersistentEnvExtensionState α σ) : σ :=
match s.state with
| some d := d
| none   := s.entries.foldl (ext.addEntryFn false) s.importedState.get

def forceState {α σ : Type} (ext : PersistentEnvExtension α σ) (env : Environment) : Environment :=
ext.toEnvExtension.modifyState env $ λ s, { state := some (ext.forceStateAux s), .. s }

def getState {α σ : Type} (ext : PersistentEnvExtension α σ) (env : Environment) : σ :=
ext.forceStateAux (ext.toEnvExtension.getState env)

end PersistentEnvExtension

private def mkPersistentEnvExtensionsRef : IO (IO.Ref (Array (PersistentEnvExtension EnvExtensionEntry EnvExtensionState))) :=
IO.mkRef Array.empty

@[init mkPersistentEnvExtensionsRef]
private constant persistentEnvExtensionsRef : IO.Ref (Array (PersistentEnvExtension EnvExtensionEntry EnvExtensionState)) := default _

unsafe def registerPersistentEnvExtensionUnsafe {α σ : Type} (name : Name) (initState : σ) (someVal : α) (addEntryFn : Bool → σ → α → σ) (toArrayFn : List α → Array α) : IO (PersistentEnvExtension α σ) :=
do
let s : PersistentEnvExtensionState α σ := {
  importedEntries := Array.empty,
  importedState   := Thunk.pure initState,
  entries         := [],
  state           := some initState },
pExts ← persistentEnvExtensionsRef.get,
when (pExts.any (λ ext, ext.name == name)) $ throw (IO.userError ("invalid environment extension, '" ++ toString name ++ "' has already been used")),
ext ← registerEnvExtension s,
let pExt : PersistentEnvExtension α σ := {
  toEnvExtension := ext,
  name           := name,
  someVal        := someVal,
  addEntryFn     := addEntryFn,
  toArrayFn      := toArrayFn
},
persistentEnvExtensionsRef.modify (λ pExts, pExts.push (unsafeCast pExt)),
pure pExt

@[implementedBy registerPersistentEnvExtensionUnsafe]
constant registerPersistentEnvExtension {α σ : Type} (name : Name) (initState : σ) (someVal : α) (addEntryFn : Bool → σ → α → σ) (toArrayFn : List α → Array α) : IO (PersistentEnvExtension α σ) := default _

/- API for creating extensions in C++.
   This API will eventually be deleted. -/

@[derive Inhabited]
def CPPExtensionState := NonScalar

@[export lean.register_extension_core]
unsafe def registerCPPExtension (initial : CPPExtensionState) : Option Nat :=
unsafeIO (do ext ← registerEnvExtension initial, pure ext.idx)

@[export lean.set_extension_core]
unsafe def setCPPExtensionState (env : Environment) (idx : Nat) (s : CPPExtensionState) : Option Environment :=
unsafeIO (do exts ← envExtensionsRef.get, pure $ (exts.get idx).setState env s)

@[export lean.get_extension_core]
unsafe def getCPPExtensionState (env : Environment) (idx : Nat) : Option CPPExtensionState :=
unsafeIO (do exts ← envExtensionsRef.get, pure $ (exts.get idx).getState env)

/- Legacy support for Modification objects -/

/- Opaque modification object. It is essentially a C `void *`.
   In Lean 3, a .olean file is essentially a collection of modification objects.
   This type represents the modification objects implemented in C++.
   We will eventually delete this type as soon as we port the remaining Lean 3
   legacy code.

   TODO: mark opaque -/
@[derive Inhabited]
def Modification := NonScalar

def regModListExtension : IO (EnvExtension (List Modification)) :=
registerEnvExtension []

@[init regModListExtension]
constant modListExtension : EnvExtension (List Modification) := default _

/- The C++ code uses this function to store the given modification object into the environment. -/
@[export lean.environment_save_modification_core]
def saveModification (env : Environment) (mod : Modification) : Environment :=
modListExtension.modifyState env $ λ mods, mod :: mods

/- mkModuleData invokes this function to convert a list of modification objects into
   a serialized byte array. -/
@[extern "lean_serialize_modifications"]
constant serializeModifications : List Modification → ByteArray := default _

/- Content of a .olean file.
   We use `compact.cpp` to generate the image of this object in disk. -/
structure ModuleData :=
(imports    : Array Name)
(constants  : Array ConstantInfo)
(entries    : Array (Name × Array EnvExtensionEntry))
(serialized : ByteArray) -- Legacy support: serialized modification objects

def mkModuleData (env : Environment) : IO ModuleData :=
do
pExts ← persistentEnvExtensionsRef.get,
let entries : Array (Name × Array EnvExtensionEntry) := pExts.size.fold
  (λ i result,
    let entryList  := (pExts.get i).getEntries env in
    let toArrayFn  := (pExts.get i).toArrayFn in
    let extName    := (pExts.get i).name in
    result.push (extName, toArrayFn entryList))
  Array.empty,
pure {
imports    := env.imports,
constants  := env.constants.foldStage2 (λ cs _ c, cs.push c) Array.empty,
entries    := entries,
serialized := serializeModifications (modListExtension.getState env)
}

end Lean
