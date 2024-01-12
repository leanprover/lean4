/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner
-/
import Lake.Util.Log
import Lake.Util.Name
import Lake.Load.Config
import Lake.Config.Workspace

open System Lean

/-! # Lake Manifest
The data structure of a Lake manifest and the definitions needed
to create, modify, serialize, and deserialize it.
-/

namespace Lake

/--
Current version of the manifest format.

**Version History**

- **v1**: first version
- **v2**: add `inputRev?` package entry field
- **v3**: change entry to inductive (with `path`/`git`)
- **v4**: add `packagesDir` manifest field
- **v5**: add `inherited` package entry field (and the removed `opts`)
- **v6**: add package root `name` manifest field
- **v7**: `type` refactor, custom to/fromJson
- **v8**: add `github` dependency
-/
@[inline] def Manifest.version : Nat := 8

/-- Manifest version 6 package entry. For compatibility. -/
inductive PackageEntryV6
| path (name : Name) (opts : NameMap String) (inherited : Bool) (dir : FilePath)
| git (name : Name) (opts : NameMap String) (inherited : Bool) (url : String) (rev : String)
    (inputRev? : Option String) (subDir? : Option FilePath)
deriving FromJson, ToJson, Inhabited

/-- Set `/` as the path separator, even on Windows. -/
def normalizePath (path : FilePath) : FilePath :=
  if System.Platform.isWindows then
    path.toString.map fun c => if c = '\\' then '/' else c
  else
    path.toString

/--
Use `/` and instead of `\\` in file paths
when serializing the manifest on Windows.
-/
local instance : ToJson FilePath where
  toJson path := toJson <| normalizePath path

/-- The package source for an entry in the manifest. -/
inductive PackageEntrySource
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
  /-- A remote GitHub package. -/
  | github
    (owner repo : String)
    (rev : String)
    (inputRev? : Option String)
    (subDir? : Option FilePath)
  deriving Inhabited

/-- An entry for a package stored in the manifest. -/
structure PackageEntry where
  name : Name
  inherited : Bool
  configFile : FilePath
  manifestFile? : Option FilePath
  source : PackageEntrySource
  deriving Inhabited

namespace PackageEntry

protected def toJson (entry : PackageEntry) : Json :=
  let fields := [
    ("name", toJson entry.name),
    ("configFile" , toJson entry.configFile),
    ("manifestFile", toJson entry.manifestFile?),
    ("inherited", toJson entry.inherited)
  ]
  let fields :=
    match entry.source with
    | .path  dir =>
      ("type", "path") :: fields.append [
        ("dir", toJson dir)
      ]
    | .git url rev inputRev? subDir? =>
      ("type", "git") :: fields.append [
        ("url", toJson url),
        ("rev", toJson rev),
        ("inputRev", toJson inputRev?),
        ("subDir", toJson subDir?)
      ]
    | .github owner repo rev inputRev? subDir? =>
      ("type", "github") :: fields.append [
        ("owner", toJson owner),
        ("repo", toJson repo),
        ("rev", toJson rev),
        ("inputRev", toJson inputRev?),
        ("subDir", toJson subDir?)
      ]
  Json.mkObj fields

instance : ToJson PackageEntry := ⟨PackageEntry.toJson⟩

protected def fromJson? (json : Json) : Except String PackageEntry := do
  let obj ← json.getObj?
  let type ← get obj "type"
  let name ← get obj "name"
  let inherited ← get obj "inherited"
  let configFile ← getD obj "configFile" defaultConfigFile
  let manifestFile ← getD obj "manifestFile" defaultManifestFile
  let source : PackageEntrySource ← id do
    match type with
    | "path" =>
      let dir ← get obj "dir"
      return .path dir
    | "git" =>
      let url ← get obj "url"
      let rev ← get obj "rev"
      let inputRev? ← get? obj "inputRev"
      let subDir? ← get? obj "subDir"
      return .git url rev inputRev? subDir?
    | "github" =>
      let owner ← get obj "owner"
      let repository ← get obj "repository"
      let rev ← get obj "rev"
      let inputRev? ← get? obj "inputRev"
      let subDir? ← get? obj "subDir"
      return .github owner repository rev inputRev? subDir?
    | _ =>
      throw s!"unknown package entry type '{type}'"
  return {name, inherited, configFile, manifestFile? := manifestFile, source}
where
  get {α} [FromJson α] obj prop : Except String α :=
    match obj.find compare prop with
    | none => throw s!"package entry missing required property '{prop}'"
    | some val => fromJson? val |>.mapError (s!"in package entry property '{prop}': {·}")
  get? {α} [FromJson α] obj prop : Except String (Option α) :=
    match obj.find compare prop with
    | none => pure none
    | some val => fromJson? val |>.mapError (s!"in package entry property '{prop}': {·}")
  getD {α} [FromJson α] obj prop (default : α) : Except String α :=
    (Option.getD · default) <$> get? obj prop

instance : FromJson PackageEntry := ⟨PackageEntry.fromJson?⟩

@[inline] def setInherited (entry : PackageEntry) : PackageEntry :=
  {entry with inherited := true}

@[inline] def setManifestFile (path? : Option FilePath) (entry : PackageEntry) : PackageEntry :=
  {entry with manifestFile? := path?}

@[inline] def inDirectory (pkgDir : FilePath) (entry : PackageEntry) : PackageEntry :=
  {entry with source := match entry.source with | .path dir => .path (pkgDir / dir) | s => s}

def ofV6 : PackageEntryV6 → PackageEntry
| .path name _opts inherited dir =>
  {name, inherited, configFile := defaultConfigFile, manifestFile? := none,
    source := .path dir}
| .git name _opts inherited url rev inputRev? subDir? =>
  {name, inherited, configFile := defaultConfigFile, manifestFile? := none,
    source := .git url rev inputRev? subDir?}

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
    ("version", version),
    ("name", toJson self.name),
    ("lakeDir", toJson self.lakeDir),
    ("packagesDir", toJson self.packagesDir?),
    ("packages", toJson self.packages)
  ]

instance : ToJson Manifest := ⟨Manifest.toJson⟩

protected def fromJson? (json : Json) : Except String Manifest := do
  let .ok obj := json.getObj?
    | throw "manifest not a JSON object"
  let ver : Json ← get obj "version"
  let .ok ver := ver.getNat?
    | throw s!"unknown manifest version '{ver}'"
  if ver < 5 then
    throw s!"incompatible manifest version '{ver}'"
  else if ver ≤ 6 then
    let name ← getD obj "name" Name.anonymous
    let lakeDir ← getD obj "lakeDir" defaultLakeDir
    let packagesDir? ← get? obj "packagesDir"
    let pkgs : Array PackageEntryV6 ← getD obj "packages" #[]
    return {name, lakeDir, packagesDir?, packages := pkgs.map PackageEntry.ofV6}
  else if ver ≤ Manifest.version then
    let name ← getD obj "name" Name.anonymous
    let lakeDir ← get obj "lakeDir"
    let packagesDir ← get obj "packagesDir"
    let packages : Array PackageEntry ← getD obj "packages" #[]
    return {name, lakeDir, packagesDir? := packagesDir, packages}
  else
    throw <|
      s!"manifest version `{ver}` is higher than this Lake's '{Manifest.version}'; " ++
      "you may need to update your `lean-toolchain`"
where
  get {α} [FromJson α] obj prop : Except String α :=
    match obj.find compare prop with
    | none => throw s!"manifest missing required property '{prop}'"
    | some val => fromJson? val |>.mapError (s!"in manifest property '{prop}': {·}")
  get? {α} [FromJson α] obj prop : Except String (Option α) :=
    match obj.find compare prop with
    | none => pure none
    | some val => fromJson? val |>.mapError (s!"in manifest property '{prop}': {·}")
  getD {α} [FromJson α] obj prop (default : α) : Except String α :=
    (Option.getD · default) <$> get? obj prop

instance : FromJson Manifest := ⟨Manifest.fromJson?⟩

/-- Parse a `Manifest` from a string. -/
def parse (s : String) : Except String Manifest := do
  match Json.parse s with
  | .ok json => fromJson? json
  | .error e => throw s!"manifest is not valid JSON: {e}"

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

/-- Save the manifest as JSON to a file. -/
def saveToFile (self : Manifest) (manifestFile : FilePath) : IO PUnit := do
  let jsonString := Json.pretty self.toJson
  IO.FS.writeFile manifestFile <| jsonString.push '\n'
