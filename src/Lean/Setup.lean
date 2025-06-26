/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mac Malone
-/
prelude
import Lean.Data.Json
import Lean.Util.LeanOptions

/-!
# Module Setup Information

Data types used by Lean module headers and the `--setup` CLI.
-/

namespace Lean

/- Abstract structure of an `import` statement. -/
structure Import where
  module     : Name
  /-- `import all`; whether to import and expose all data saved by the module. -/
  importAll  : Bool := false
  /-- Whether to activate this import when the current module itself is imported. -/
  isExported : Bool := true
  /-- Whether all definitions (transitively) reachable through the -/
  isMeta     : Bool := false
  deriving Repr, Inhabited, ToJson, FromJson

instance : Coe Name Import := ⟨({module := ·})⟩

instance : ToString Import := ⟨fun imp => toString imp.module⟩

/-- Abstract structure of a module's header. -/
structure ModuleHeader where
  /-- The module's direct imports (i.e., those listed in the header). -/
  imports  : Array Import
  /-- Whether the module is participating in the module system. -/
  isModule : Bool
  deriving Repr, Inhabited, ToJson, FromJson

/--
Module data files used for an `import` statement.
This structure is designed for efficient JSON serialization.
-/
structure ImportArtifacts where
  oleanParts : Array System.FilePath
  deriving Repr, Inhabited

instance : ToJson ImportArtifacts := ⟨(toJson ·.oleanParts)⟩
instance : FromJson ImportArtifacts := ⟨(.mk <$> fromJson? ·)⟩

def ImportArtifacts.olean? (arts : ImportArtifacts) :=
  arts.oleanParts[0]?

def ImportArtifacts.oleanServer? (arts : ImportArtifacts) :=
  arts.oleanParts[1]?

def ImportArtifacts.oleanPrivate? (arts : ImportArtifacts) :=
  arts.oleanParts[2]?

/-- Files containing data for a single module. -/
structure ModuleArtifacts where
  lean? : Option System.FilePath := none
  olean? : Option System.FilePath := none
  oleanServer? : Option System.FilePath := none
  oleanPrivate? : Option System.FilePath := none
  ilean? : Option System.FilePath := none
  c? : Option System.FilePath := none
  bc? : Option System.FilePath := none
  deriving Repr, Inhabited, ToJson, FromJson

def ModuleArtifacts.oleanParts (arts : ModuleArtifacts) : Array System.FilePath := Id.run do
  let mut fnames := #[]
  if let some mFile := arts.olean? then
    fnames := fnames.push mFile
    if let some sFile := arts.oleanServer? then
      fnames := fnames.push sFile
      if let some pFile := arts.oleanPrivate? then
        fnames := fnames.push pFile
  return fnames

/-- A module's setup information as described by a JSON file. -/
structure ModuleSetup where
  /-- Name of the module. -/
  name : Name
  /--
  Whether the module, by default, participates in the module system.
  Even if `false`, a module can still choose to participate by using `module` in its header.
  -/
  isModule : Bool := false
  /--
  The module's direct imports.
  If `none`, uses the imports from the module header.
  -/
  imports? : Option (Array Import) := none
  /-- Pre-resolved artifacts of transitively imported modules. -/
  importArts : NameMap ImportArtifacts := {}
  /-- Dynamic libraries to load with the module. -/
  dynlibs : Array System.FilePath := #[]
  /-- Plugins to initialize with the module. -/
  plugins : Array System.FilePath := #[]
  /-- Additional options for the module. -/
  options : LeanOptions := {}
  deriving Repr, Inhabited, ToJson, FromJson

/-- Load a `ModuleSetup` from a JSON file. -/
def ModuleSetup.load (path : System.FilePath) : IO ModuleSetup := do
  let contents ← IO.FS.readFile path
  match Json.parse contents >>= fromJson? with
  | .ok info => pure info
  | .error msg => throw <| IO.userError s!"failed to load header from {path}: {msg}"
