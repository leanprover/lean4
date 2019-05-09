/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.io
import init.util
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
(initState       : Thunk ExtensionState)
(entries         : List ExtensionEntry   := [])
(state           : Option ExtensionState := none)

instance envExtensionDataInh : Inhabited EnvExtensionData :=
⟨{ importedEntries := Array.empty, initState := Thunk.mk (default _) }⟩

structure Environment :=
(const2ModId : HashMap Name ModuleId)
(constants   : SMap Name ConstantInfo Name.quickLt)
(extensions  : Array EnvExtensionData)
(trustLevel  : UInt32 := 0)
(quotInit    : Bool := false)

instance envInh : Inhabited Environment :=
⟨{ const2ModId := {}, constants := {}, extensions := Array.empty }⟩

structure EnvExtension (α : Type) (σ : Type) :=
(name      : Name)
(idx       : Nat)
(initState : σ)
(addEntry  : Bool → Environment → σ → α → σ)
(toArray   : List α → Array α)

@[export leanGetModuleEntriesUnsafe]
unsafe def getModuleEntriesUnsafe {α σ : Type} (ext : EnvExtension α σ) (env : Environment) (m : ModuleId) : Array α :=
let entries := (env.extensions.get ext.idx).importedEntries.get m.id in
unsafeCast entries

@[extern "leanGetModuleEntriesUnsafe"]
constant getModuleEntries {α σ : Type} (ext : EnvExtension α σ) (env : Environment) (m : ModuleId) : Array α := default _

private def releaseExtensionData (env : Environment) (extIdx : Nat) : Environment :=
{ extensions := env.extensions.set extIdx (default _), .. env }

private def setExtensionData (env : Environment) (extIdx : Nat) (d : EnvExtensionData) : Environment :=
{ extensions := env.extensions.set extIdx d, .. env }

@[export leanAddEntryUnsafe]
unsafe def addEntryUnsafe {α σ : Type} (ext : EnvExtension α σ) (env : Environment) (a : α) : Environment :=
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
  let s : σ   := @unsafeCast _ _ ⟨ext.initState⟩ s in
  let s       := ext.addEntry false env s a in
  let extData := { state := unsafeCast s, .. extData } in
  setExtensionData env extIdx extData

@[extern "leanAddEntryUnsafe"]
constant addEntry {α σ : Type} (ext : EnvExtension α σ) (env : Environment) (a : α) : Environment := default _

-- unsafe def getStateUnsafe {α σ : Type} (ext : EnvExtension α σ) (env : Environment)

end Lean
