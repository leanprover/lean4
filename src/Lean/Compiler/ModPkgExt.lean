/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Environment

set_option doc.verso true

namespace Lean

/-- Persistent environment extension for storing a single serializable value per module. -/
@[expose] public def ModuleEnvExtension (σ : Type) := PersistentEnvExtension σ σ σ

public def registerModuleEnvExtension
  [Inhabited σ] (mkInitial : IO σ) (name : Name := by exact decl_name%)
: IO (ModuleEnvExtension σ) :=
  registerPersistentEnvExtension {
    name            := name
    mkInitial       := mkInitial
    addImportedFn   := fun _ _ => mkInitial
    addEntryFn      := fun s _ => s
    exportEntriesFn := fun s => #[s]
  }

namespace ModuleEnvExtension

public instance [Inhabited σ] : Inhabited (ModuleEnvExtension σ) :=
  inferInstanceAs (Inhabited (PersistentEnvExtension ..))

public def getStateByIdx? [Inhabited σ] (ext : ModuleEnvExtension σ) (env : Environment) (idx : ModuleIdx) : Option σ :=
  (ext.getModuleEntries env idx)[0]?

end ModuleEnvExtension

private initialize modPkgExt : ModuleEnvExtension (Option PkgId) ←
  registerModuleEnvExtension (pure none)

/-- Returns the package (if any) of an imported module (by its index). -/
public def Environment.getModulePackageByIdx? (env : Environment) (idx : ModuleIdx) : Option PkgId :=
  modPkgExt.getStateByIdx? env idx |>.join

/-- Returns the package (if any) of the current module. -/
@[inline] public def Environment.getModulePackage? (env : Environment) : Option PkgId :=
  modPkgExt.getState env

/-- Sets the package of the current module. -/
@[inline] public def Environment.setModulePackage (pkg? : Option PkgId) (env : Environment) : Environment :=
  modPkgExt.setState env pkg?
