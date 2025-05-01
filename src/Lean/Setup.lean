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

structure Import where
  module        : Name
  /-- `import all`; whether to import and expose all data saved by the module. -/
  importAll : Bool := false
  /-- Whether to activate this import when the current module itself is imported. -/
  isExported    : Bool := true
  deriving Repr, Inhabited, ToJson, FromJson

instance : Coe Name Import := ⟨({module := ·})⟩

instance : ToString Import := ⟨fun imp => toString imp.module⟩

/-- Files containing data for a single module. -/
structure ModuleArtifacts where
  lean? : Option System.FilePath := none
  olean? : Option System.FilePath := none
  oleanServer? : Option System.FilePath := none
  oleanPrivate? : Option System.FilePath := none
  ilean? : Option System.FilePath := none
  deriving Repr, Inhabited, ToJson, FromJson

/--
A module's setup information as described by a JSON file.
Supercedes the module's header when the `--setup` CLI option is used.
-/
structure ModuleSetup where
  /-- Name of the module. -/
  name : Name
  /-- Whether the module is participating in the module system. -/
  isModule : Bool := false
  /- The module's direct imports. -/
  imports : Array Import := #[]
  /-- Pre-resolved artifacts of related modules (e.g., this module's transitive imports). -/
  modules : NameMap ModuleArtifacts := {}
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
