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
/- Opaque ExtensionEntry -/
constant ExtensionEntryPointed : PointedType := default _
def ExtensionEntry : Type := ExtensionEntryPointed.type
instance extEntryInh : Inhabited ExtensionEntry := ⟨ExtensionEntryPointed.val⟩

/- Opaque ExtensionState -/
constant ExtensionStatePointed : PointedType := default _
def ExtensionState : Type := ExtensionStatePointed.type
instance extStateInh : Inhabited ExtensionState := ⟨ExtensionStatePointed.val⟩

structure ModuleId :=
(id : Nat)

@[inline] def ModuleId.beq (m₁ m₂ : ModuleId) := m₁.id == m₂.id
instance moduleidHasBeq : HasBeq ModuleId := ⟨ModuleId.beq⟩

/- Environment Extension Data -/
structure EnvExtensionData :=
(importedEntries : Array (Array ExtensionEntry))
(importedState   : Thunk ExtensionState)
(entries         : List ExtensionEntry   := [])
(state           : Option ExtensionState := none)

instance envExtensionDataInh : Inhabited EnvExtensionData :=
⟨{ importedEntries := Array.empty, importedState := Thunk.mk (default _) }⟩

/- TODO: mark opaque. -/
structure Environment :=
(const2ModId : HashMap Name ModuleId)
(constants   : SMap Name ConstantInfo Name.quickLt)
(extensions  : Array EnvExtensionData)
(trustLevel  : UInt32 := 0)
(quotInit    : Bool := false)
(imports     : Array Name := Array.empty)

instance envInh : Inhabited Environment :=
⟨{ const2ModId := {}, constants := {}, extensions := Array.empty }⟩

/- TODO: mark opaque. -/
structure EnvExtension (α : Type) (σ : Type) :=
(name      : Name)
(idx       : Nat)
(initState : σ)
(someVal   : α)
(addEntry  : Bool → σ → α → σ)
(toArray   : List α → Array α)

instance envExtDefInh : Inhabited (EnvExtension ExtensionEntry ExtensionState) :=
⟨{ name    := default _, idx := 0, initState := default _,
   someVal := default _, addEntry := λ _ s _, s,
   toArray := λ l, l.toArray }⟩

private def mkEnvExtensionsRef : IO (IO.Ref (Array (EnvExtension ExtensionEntry ExtensionState))) :=
IO.mkRef Array.empty

@[init mkEnvExtensionsRef]
private constant envExtensionsRef : IO.Ref (Array (EnvExtension ExtensionEntry ExtensionState)) := default _

unsafe def registerEnvExtensionUnsafe {α σ : Type} (name : Name) (initState : σ) (someVal : α) (addEntry : Bool → σ → α → σ) (toArray : List α → Array α) : IO (EnvExtension α σ) :=
do
exts ← envExtensionsRef.get,
when (exts.any (λ ext, ext.name == name)) $ throw (IO.userError ("invalid environment extension, '" ++ toString name ++ "' has already been used")),
let idx := exts.size,
let ext : EnvExtension α σ := {
   name      := name,
   idx       := idx,
   initState := initState,
   someVal   := someVal,
   addEntry  := addEntry,
   toArray   := toArray
},
envExtensionsRef.modify (λ exts, exts.push (unsafeCast ext)),
pure ext

@[implementedBy registerEnvExtensionUnsafe]
constant registerEnvExtension {α σ : Type} (name : Name) (initState : σ) (someVal : α) (addEntry : Bool → σ → α → σ) (toArray : List α → Array α) : IO (EnvExtension α σ) := default _

def mkEmptyEnvironment (trustLevel : UInt32 := 0) : IO Environment :=
do exts ← envExtensionsRef.get,
pure { const2ModId := {},
       constants   := {},
       trustLevel  := trustLevel,
       extensions  := exts.map $ λ ext, {
          importedEntries := Array.empty,
          importedState   := Thunk.pure ext.initState
       }
}

unsafe def getModuleEntriesUnsafe {α σ : Type} (env : Environment) (ext : EnvExtension α σ) (m : ModuleId) : Array α :=
let entries := (env.extensions.get ext.idx).importedEntries.get m.id in
unsafeCast entries

@[implementedBy getModuleEntriesUnsafe]
constant getModuleEntries {α σ : Type} (env : Environment) (ext : EnvExtension α σ) (m : ModuleId) : Array α := default _

private def releaseExtensionData (env : Environment) (extIdx : Nat) : Environment :=
{ extensions := env.extensions.set extIdx (default _), .. env }

private def setExtensionData (env : Environment) (extIdx : Nat) (d : EnvExtensionData) : Environment :=
{ extensions := env.extensions.set extIdx d, .. env }

unsafe def addEntryUnsafe {α σ : Type} (env : Environment) (ext : EnvExtension α σ) (a : α) : Environment :=
let extIdx  := ext.idx in
let extData := env.extensions.get extIdx in
let env     := releaseExtensionData env extIdx in
let entries : List ExtensionEntry := (unsafeCast a) :: extData.entries in
match extData.state with
| none :=
  let extData := { entries := entries, .. extData } in
  setExtensionData env extIdx extData
| some s :=
  let extData := { state := none, .. extData } in
  let s       := ext.addEntry false (@unsafeCast _ _ ⟨ext.initState⟩ s) a in
  let extData := { state := some (unsafeCast s), .. extData } in
  setExtensionData env extIdx extData

@[implementedBy addEntryUnsafe]
constant addEntry {α σ : Type} (env : Environment) (ext : EnvExtension α σ) (a : α) : Environment := default _

unsafe def mkExtensionState {α σ : Type} (extData : EnvExtensionData) (ext : EnvExtension α σ) : ExtensionState :=
let importedState := extData.importedState.get in
extData.entries.foldl
  (λ s e, unsafeCast (ext.addEntry false (@unsafeCast _ _ ⟨ext.initState⟩ s) (@unsafeCast _ _ ⟨ext.someVal⟩ e)))
  importedState

unsafe def initExtensionStateUnsafe {α σ : Type} (env : Environment) (ext : EnvExtension α σ) : Environment :=
let extIdx  := ext.idx in
let extData := env.extensions.get extIdx in
if extData.state.isSome then env
else
  let env     := releaseExtensionData env extIdx in
  let s       := mkExtensionState extData ext in
  let extData := { state := some s, .. extData } in
  setExtensionData env extIdx extData

@[implementedBy initExtensionStateUnsafe]
constant initExtensionState {α σ : Type} (env : Environment) (ext : EnvExtension α σ) : Environment := default _

unsafe def getExtensionStateUnsafe {α σ : Type} (env : Environment) (ext : EnvExtension α σ) : σ :=
let extIdx  := ext.idx in
let extData := env.extensions.get extIdx in
match extData.state with
| some s := @unsafeCast _ _ ⟨ext.initState⟩ s
| none   :=
  let s := mkExtensionState extData ext in
  @unsafeCast _ _ ⟨ext.initState⟩ s

@[implementedBy getExtensionStateUnsafe]
constant getExtensionState {α σ : Type} (env : Environment) (ext : EnvExtension α σ) : σ := ext.initState

structure ModuleData :=
(imports    : Array Name)
(constants  : Array ConstantInfo)
(entries    : Array (Name × Array ExtensionEntry))
(serialized : ByteArray) -- legacy

def mkModuleData (env : Environment) : IO ModuleData :=
do
exts ← envExtensionsRef.get,
let entries : Array (Name × Array ExtensionEntry) := exts.size.fold
  (λ i result,
    let entryList  := (env.extensions.get i).entries in
    let toArrayFn  := (exts.get i).toArray in
    let extName   := (exts.get i).name in
    result.push (extName, toArrayFn entryList))
  Array.empty,
pure {
imports    := env.imports,
constants  := env.constants.foldStage2 (λ cs _ c, cs.push c) Array.empty,
entries    := entries,
serialized := ByteArray.empty
}

end Lean
