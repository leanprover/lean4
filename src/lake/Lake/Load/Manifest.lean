/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner
-/
prelude
import Lake.Util.Log
import Lake.Util.Name
import Lake.Util.FilePath
import Lake.Util.JsonObject
import Lake.Util.Version
import Lake.Config.Defaults

open System Lean

/-! # Lake Manifest
The data structure of a Lake manifest and the definitions needed
to create, modify, serialize, and deserialize it.
-/

namespace Lake

/--
The current version of the manifest format.

Three-part semantic versions were introduced in `v1.0.0`.
Major version increments indicate breaking changes
(e.g., new required fields and semantic changes to existing fields).
Minor version increments (after `0.x`) indicate backwards-compatible extensions
(e.g., adding optional fields, removing fields).

Lake supports reading manifests with versions that have `-` suffixes.
When checking for version compatibility, Lake expects a manifest with version
`x.y.z-foo` to have all the features of the official manifest version `x.y.z`.
That is, Lake ignores the `-` suffix.

**VERSION HISTORY**

**v0.x.0** (versioned by a natural number)
- `1`: First version
- `2`: Adds optional `inputRev` package entry field
- `3`: Changes entry to inductive (with `path`/`git`)
- `4`: Adds required `packagesDir` manifest field
- `5`: Adds optional `inherited` package entry field (and removed `opts`)
- `6`: Adds optional package root `name` manifest field
- `7`: `type` refactor, custom to/fromJson

**v1.x.x** (versioned by a string)
- `"1.0.0"`: Switches to a semantic versioning scheme
- `"1.1.0"`: Add optional `scope` package entry field
-/
@[inline] def Manifest.version : StdVer := {major := 1, minor := 1}

/-- Manifest version `0.6.0` package entry. For backwards compatibility. -/
inductive PackageEntryV6
| path (name : Name) (opts : NameMap String) (inherited : Bool) (dir : FilePath)
| git (name : Name) (opts : NameMap String) (inherited : Bool) (url : String) (rev : String)
    (inputRev? : Option String) (subDir? : Option FilePath)
deriving FromJson, ToJson, Inhabited

/--
The package source for an entry in the manifest.
Describes exactly how Lake should materialize the package.
-/
inductive PackageEntrySrc
  /--
  A local filesystem package. `dir` is relative to the package directory
  of the package containing the manifest.
  -/
  | path
    (dir : FilePath)
  /-- A remote Git package. -/
  | git
    (url : String)
    (rev : String)
    (inputRev? : Option String)
    (subDir? : Option FilePath)
  deriving Inhabited

/-- An entry for a package stored in the manifest. -/
structure PackageEntry where
  name : Name
  scope : String := ""
  inherited : Bool
  configFile : FilePath := defaultConfigFile
  manifestFile? : Option FilePath := none
  src : PackageEntrySrc
  deriving Inhabited

namespace PackageEntry

protected def toJson (entry : PackageEntry) : Json :=
  let fields := [
    ("name", toJson entry.name),
    ("scope", toJson entry.scope),
    ("configFile" , toJson entry.configFile),
    ("manifestFile", toJson entry.manifestFile?),
    ("inherited", toJson entry.inherited),
  ]
  let fields :=
    match entry.src with
    | .path  dir =>
      ("type", "path") :: fields.append [
        ("dir", toJson dir),
      ]
    | .git url rev inputRev? subDir? =>
      ("type", "git") :: fields.append [
        ("url", toJson url),
        ("rev", toJson rev),
        ("inputRev", toJson inputRev?),
        ("subDir", toJson subDir?),
      ]
  Json.mkObj fields

instance : ToJson PackageEntry := ⟨PackageEntry.toJson⟩

protected def fromJson? (json : Json) : Except String PackageEntry := do
  let obj ← JsonObject.fromJson? json |>.mapError (s!"package entry: {·}")
  let name ← obj.get "name" |>.mapError (s!"package entry: {·}")
  let scope ← obj.getD "scope" ""
  try
    let type ← obj.get "type"
    let inherited ← obj.get "inherited"
    let configFile ← obj.getD "configFile" defaultConfigFile
    let manifestFile ← obj.getD "manifestFile" defaultManifestFile
    let src : PackageEntrySrc ← id do
      match type with
      | "path" =>
        let dir ← obj.get "dir"
        return .path dir
      | "git" =>
        let url ← obj.get "url"
        let rev ← obj.get "rev"
        let inputRev? ← obj.get? "inputRev"
        let subDir? ← obj.get? "subDir"
        return .git url rev inputRev? subDir?
      | _ =>
        throw s!"unknown package entry type '{type}'"
    return {
      name, scope, inherited,
      configFile, manifestFile? := manifestFile, src
      : PackageEntry
    }
  catch e =>
    throw s!"package entry '{name}': {e}"

instance : FromJson PackageEntry := ⟨PackageEntry.fromJson?⟩

@[inline] def setInherited (entry : PackageEntry) : PackageEntry :=
  {entry with inherited := true}

@[inline] def setConfigFile (path : FilePath) (entry : PackageEntry) : PackageEntry :=
  {entry with configFile := path}

@[inline] def setManifestFile (path? : Option FilePath) (entry : PackageEntry) : PackageEntry :=
  {entry with manifestFile? := path?}

@[inline] def inDirectory (pkgDir : FilePath) (entry : PackageEntry) : PackageEntry :=
  {entry with src := match entry.src with | .path dir => .path (pkgDir / dir) | s => s}

def ofV6 : PackageEntryV6 → PackageEntry
| .path name _opts inherited dir =>
  {name, inherited, src := .path dir}
| .git name _opts inherited url rev inputRev? subDir? =>
  {name, inherited, src := .git url rev inputRev? subDir?}

end PackageEntry

/-- Manifest data structure that is serialized to the file. -/
structure Manifest where
  name : Name
  lakeDir : FilePath
  packagesDir? : Option FilePath := none
  packages : Array PackageEntry := #[]

namespace Manifest

/-- Add a package entry to the end of a manifest. -/
def addPackage (entry : PackageEntry) (self : Manifest) : Manifest :=
  {self with packages := self.packages.push entry}

protected def toJson (self : Manifest) : Json :=
  Json.mkObj [
    ("version", toJson version),
    ("name", toJson self.name),
    ("lakeDir", toJson self.lakeDir),
    ("packagesDir", toJson self.packagesDir?),
    ("packages", toJson self.packages),
  ]

instance : ToJson Manifest := ⟨Manifest.toJson⟩

def getVersion (obj : JsonObject) : Except String SemVerCore := do
  let ver : Json ← obj.get "version" <|> obj.get "schemaVersion"
  let ver : SemVerCore ←
    match ver with
    | (n : Nat) => pure {minor := n}
    | (s : String) => StdVer.parse s
    | ver => throw s!"invalid version '{ver}'; \
      you may need to update your 'lean-toolchain'"
  if ver.major > 1 then
    throw s!"schema version '{ver}' is of a higher major version than this \
      Lake's '{Manifest.version}'; you may need to update your 'lean-toolchain'"
  else if ver < {minor := 5} then
    throw s!"incompatible manifest version '{ver}'"
  else
    return ver

def getPackages (ver : StdVer) (obj : JsonObject) : Except String (Array PackageEntry) := do
  if ver < {minor := 7} then
    (·.map PackageEntry.ofV6) <$> obj.getD "packages" #[]
  else
    obj.getD "packages" #[]

protected def fromJson? (json : Json) : Except String Manifest := do
  let obj ← JsonObject.fromJson? json
  let ver ← getVersion obj
  let name ← obj.getD "name" Name.anonymous
  let lakeDir ← obj.getD "lakeDir" defaultLakeDir
  let packagesDir? ← obj.get? "packagesDir"
  let packages ← getPackages ver obj
  return {name, lakeDir, packagesDir?, packages}

instance : FromJson Manifest := ⟨Manifest.fromJson?⟩

/-- Parse a `Manifest` from a string. -/
def parse (data : String) : Except String Manifest := do
  match Json.parse data with
  | .ok json => fromJson? json
  | .error e => throw s!"invalid JSON: {e}"

/-- Parse a manifest file. -/
def load (file : FilePath) : IO Manifest := do
  let contents ← IO.FS.readFile file
  match inline <| Manifest.parse contents with
  | .ok a => return a
  | .error e => error s!"{file}: {e}"

/--
Parse a manifest file. Returns `none` if the file does not exist.
Errors if the manifest is ill-formatted or the read files for other reasons.
-/
def load? (file : FilePath) : IO (Option Manifest) := do
  match (← inline (load file) |>.toBaseIO) with
  | .ok contents => return contents
  | .error (.noFileOrDirectory ..) => return none
  | .error e => throw e

/-- Serialize the manifest to a JSON file. -/
def save (self : Manifest) (manifestFile : FilePath) : IO PUnit := do
  let contents := Json.pretty self.toJson
  IO.FS.writeFile manifestFile <| contents.push '\n'

@[deprecated save (since := "2024-12-17")] abbrev saveToFile := @save

/-- Deserialize package entries from a (partial) JSON manifest. -/
def decodeEntries (data : Json)  : Except String (Array PackageEntry) := do
  let obj ← JsonObject.fromJson? data
  getPackages (← getVersion obj) obj

/-- Deserialize manifest package entries from a JSON string. -/
def parseEntries (data : String) : Except String (Array PackageEntry) := do
  match Json.parse data with
  | .ok json => decodeEntries json
  | .error e => throw s!"invalid JSON: {e}"

/-- Deserialize manifest package entries from a JSON file. -/
def loadEntries (file : FilePath) : IO (Array PackageEntry) := do
  let contents ← IO.FS.readFile file
  match inline <| parseEntries contents with
  | .ok a => return a
  | .error e => error s!"{file}: {e}"

/--
Deserialize manifest package entries from a JSON file.
Returns an empty array if the file does not exist.
-/
def tryLoadEntries (file : FilePath) : IO (Array PackageEntry) := do
  match  (← inline (loadEntries file) |>.toBaseIO) with
  | .ok a => return a
  | .error (.noFileOrDirectory ..) => return #[]
  | .error e => error s!"{file}: {e}"

/-- Serialize manifest package entries to a JSON file. -/
def saveEntries (file : FilePath) (entries : Array PackageEntry)  : IO PUnit := do
  let contents := Json.pretty <| Json.mkObj [
    ("schemaVersion", toJson version),
    ("packages", toJson entries)
  ]
  IO.FS.writeFile file <| contents.push '\n'
