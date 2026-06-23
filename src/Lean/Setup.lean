/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mac Malone
-/
module

prelude
public import Lean.Data.Json.Parser
public import Lean.Util.LeanOptions

set_option doc.verso true

public section

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
  /-- Whether to import IR for all definitions (transitively) reachable. -/
  isMeta     : Bool := false
  deriving Repr, Inhabited, ToJson, FromJson,
    BEq, Hashable -- needed by Lake (in `Lake.Load.Elab.Lean`)

-- TODO: move further up into `Init` by using simpler representation for `imports`
@[extern "lean_idbg_client_loop"]
opaque Idbg.idbgClientLoop {α : Type} [Nonempty α]
  (siteId : String) (imports : Array Import) (apply : α → String) : IO Unit

instance : Coe Name Import := ⟨({module := ·})⟩

instance : ToString Import := ⟨fun imp =>
  s!"{if imp.isExported then "public " else ""}{if imp.isMeta then "meta " else ""}import \
    {if imp.importAll then "all " else ""}{imp.module}"⟩

/-- Phases for which some IR is available for execution. -/
inductive IRPhases where
  /-- Available for execution in the final native code. -/
  | runtime
  /-- Available for execution during elaboration. -/
  | comptime
  /-- Available during run time and compile time. -/
  | all
deriving Inhabited, BEq, Repr

/-- Abstract structure of a module's header. -/
structure ModuleHeader where
  /-- The module's direct imports (i.e., those listed in the header). -/
  imports  : Array Import
  /-- Whether the module is participating in the module system. -/
  isModule : Bool
  deriving Repr, Inhabited, ToJson, FromJson

/--
Module data files used for an {lit}`import` statement.
This structure is designed for efficient JSON serialization.
-/
structure ImportArtifacts where
  ofArrays ::
    /--
    Two nested arrays of variable size: {lit}`#[#[olean, oleanServer?, oleanPrivate?], #[irSig, ir?]]`
    -/
    toArrays : Array (Array System.FilePath)
  deriving Repr, Inhabited

instance : ToJson ImportArtifacts := ⟨(toJson ·.toArrays)⟩
instance : FromJson ImportArtifacts := ⟨(.ofArrays <$> fromJson? ·)⟩

def ImportArtifacts.olean? (arts : ImportArtifacts) : Option System.FilePath :=
  arts.toArrays[0]?.bind (·[0]?)

def ImportArtifacts.oleanServer? (arts : ImportArtifacts) : Option System.FilePath :=
  arts.toArrays[0]?.bind (·[1]?)

def ImportArtifacts.oleanPrivate? (arts : ImportArtifacts) : Option System.FilePath :=
  arts.toArrays[0]?.bind (·[2]?)

def ImportArtifacts.irSig? (arts : ImportArtifacts) : Option System.FilePath :=
  arts.toArrays[1]?.bind (·[0]?)

def ImportArtifacts.ir? (arts : ImportArtifacts) : Option System.FilePath :=
  arts.toArrays[1]?.bind (·[1]?)

def ImportArtifacts.oleanParts (inServer : Bool) (arts : ImportArtifacts) : Array System.FilePath := Id.run do
  let mut fnames := #[]
  if let some mFile := arts.olean? then
    fnames := fnames.push mFile
    if let some sFile := arts.oleanServer? then
      -- For uniformity, Lake always provides us with .olean.server, so load it only when we are in
      -- server mode or we need it to load further files.
      if inServer || arts.oleanPrivate?.isSome then
        fnames := fnames.push sFile
      if let some pFile := arts.oleanPrivate? then
        fnames := fnames.push pFile
  return fnames

def ImportArtifacts.irParts (arts : ImportArtifacts) : Array System.FilePath :=
  arts.toArrays[1]?.getD #[]

/-- Files containing data for a single module. -/
structure ModuleArtifacts where
  lean? : Option System.FilePath := none
  olean? : Option System.FilePath := none
  oleanServer? : Option System.FilePath := none
  oleanPrivate? : Option System.FilePath := none
  ilean? : Option System.FilePath := none
  irSig? : Option System.FilePath := none
  ir? : Option System.FilePath := none
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

def ModuleArtifacts.irParts (arts : ModuleArtifacts) : Array System.FilePath := Id.run do
  let mut fnames := #[]
  if let some irSigFile := arts.irSig? then
    fnames := fnames.push irSigFile
    if let some irFile := arts.ir? then
      fnames := fnames.push irFile
  return fnames

/-- A Lean plugin. Plugins are shared libraries with an initialization function. -/
structure Plugin where
  /-- The path to the plugin's shared library. -/
  path : System.FilePath
  /--
  The name of the plugin initialization function symbol.
  If {lean}`none`, the symbol is derived from the file name of the shared library.
  -/
  initFn? : Option String
  deriving Repr, ToJson

namespace Plugin

/--
Constructs a plugin from just a shared library's {lean}`path`,
inferring the name of the initialization function from the library's name.
-/
def ofFilePath (path : System.FilePath) : Plugin :=
  {path, initFn? := none}

instance : Coe System.FilePath Plugin := ⟨ofFilePath⟩

protected def fromJson? (data : Json) : Except String Plugin := do
  match data with
  | .str path =>
    return .ofFilePath path
  | data@(.obj _) =>
    let path ← data.getObjValAs? _ "path"
    let initFn? ← data.getObjValAs? _ "initFn"
    return {path, initFn?}
  | _ =>
    throw "expected string or object"

instance : FromJson Plugin := ⟨Plugin.fromJson?⟩

end Plugin

/--
The type of module package identifiers.

This is a {name}`String` that is used to disambiguate native symbol prefixes between
different packages (and different versions of the same package).
-/
abbrev PkgId := String

/-- A module's setup information as described by a JSON file. -/
structure ModuleSetup where
  /-- The name of the module. -/
  name : Name
  /-- The package to which the module belongs (if any). -/
  package? : Option PkgId := none
  /--
  Whether the module, by default, participates in the module system.
  Even if {lean}`false`, a module can still choose to participate by using
  {lit}`module` in its header.
  -/
  isModule : Bool := false
  /--
  The module's direct imports.
  If {lean}`none`, uses the imports from the module header.
  -/
  imports? : Option (Array Import) := none
  /-- Pre-resolved artifacts of transitively imported modules. -/
  importArts : NameMap ImportArtifacts := {}
  /-- Dynamic libraries to load with the module. -/
  dynlibs : Array System.FilePath := #[]
  /-- Plugins to initialize with the module. -/
  plugins : Array Plugin := #[]
  /-- Additional options for the module. -/
  options : LeanOptions := {}
  deriving Repr, Inhabited, ToJson, FromJson

/-- Load a {lean}`ModuleSetup` from a JSON file. -/
def ModuleSetup.load (path : System.FilePath) : IO ModuleSetup := do
  let contents ← IO.FS.readFile path
  match Json.parse contents >>= fromJson? with
  | .ok info => pure info
  | .error msg => throw <| IO.userError s!"failed to load header from {path}: {msg}"
