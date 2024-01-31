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
- **v8**:  add package entry types `github` & `registry`,
  add `fullName` & `conditional` field, no escape in manifest `name`
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
  /-- A remote GitHub package. -/
  | github
    (owner repo : String)
    (rev : String)
    (inputRev? : Option String)
    (subDir? : Option FilePath)
  /-- A package from the default registry (e.g., Reservoir). -/
  | registry
    (rev : String)
    (inputRev? : Option String)
  deriving Inhabited

/-- An entry for a package stored in the manifest. -/
structure PackageEntry where
  name : SimpleName
  fullName : SimpleName
  inherited : Bool
  conditional : Bool := false
  configFile : FilePath := defaultConfigFile
  manifestFile? : Option FilePath := none
  source : PackageEntrySrc
  deriving Inhabited

abbrev JsonObject :=
  RBNode String (fun _ => Json)

namespace JsonObject

@[inline] protected def toJson (obj : JsonObject) : Json :=
  .obj obj

instance : ToJson JsonObject := ⟨JsonObject.toJson⟩

@[inline] protected def fromJson? (json : Json) : Except String JsonObject :=
  json.getObj?

instance : FromJson JsonObject := ⟨JsonObject.fromJson?⟩

@[inline] nonrec def erase (obj : JsonObject) (prop : String) : JsonObject :=
  obj.erase compare prop

@[inline] def getJson? (obj : JsonObject) (prop : String) : Option Json :=
  obj.find compare prop

@[inline] def get [FromJson α] (obj : JsonObject) (prop : String) : Except String α :=
  match obj.getJson? prop with
  | none => throw s!"property not found: {prop}"
  | some val => fromJson? val |>.mapError (s!"{prop}: {·}")

@[inline] def get? [FromJson α] (obj : JsonObject) (prop : String) : Except String (Option α) :=
  match obj.getJson? prop with
  | none => pure none
  | some val => fromJson? val |>.mapError (s!"{prop}: {·}")

@[inline] def getD  [FromJson α] (obj : JsonObject) (prop : String) (default : α) : Except String α :=
  (Option.getD · default) <$> obj.get? prop

end JsonObject

namespace PackageEntry

protected def toJson (entry : PackageEntry) : Json :=
  let fields := [
    ("name", toJson entry.name),
    ("fullName", toJson entry.fullName),
    ("configFile" , toJson entry.configFile),
    ("manifestFile", toJson entry.manifestFile?),
    ("conditional", toJson entry.conditional),
    ("inherited", toJson entry.inherited),
  ]
  let fields :=
    match entry.source with
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
    | .github owner repo rev inputRev? subDir? =>
      ("type", "github") :: fields.append [
        ("owner", toJson owner),
        ("repo", toJson repo),
        ("rev", toJson rev),
        ("inputRev", toJson inputRev?),
        ("subDir", toJson subDir?),
      ]
    | .registry rev inputRev? =>
      ("type", "registry") :: fields.append [
        ("rev", toJson rev),
        ("inputRev", toJson inputRev?),
      ]
  Json.mkObj fields

instance : ToJson PackageEntry := ⟨PackageEntry.toJson⟩

protected def fromJson? (json : Json) : Except String PackageEntry := do
  let obj ← JsonObject.fromJson? json |>.mapError (s!"package entry: {·}")
  let name ← obj.get "name" |>.mapError (s!"package entry: {·}")
  let fullName ← obj.getD "fullName" name
  try
    let type ← obj.get "type"
    let inherited : Bool ← obj.get "inherited"
    let conditional ← obj.getD "conditional" false
    let configFile ← obj.getD "configFile" defaultConfigFile
    let manifestFile ← obj.getD "manifestFile" defaultManifestFile
    let source : PackageEntrySrc ← id do
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
      | "github" =>
        let owner ← obj.get "owner"
        let repo ← obj.get "repo"
        let rev ← obj.get "rev"
        let inputRev? ← obj.get? "inputRev"
        let subDir? ← obj.get? "subDir"
        return .github owner repo rev inputRev? subDir?
      | "registry" =>
        let rev ← obj.get "rev"
        let inputRev? ← obj.get? "inputRev"
        return .registry rev inputRev?
      | _ =>
        throw s!"unknown package entry type '{type}'"
    return {
      name, fullName, inherited, conditional,
      configFile, manifestFile? := manifestFile, source : PackageEntry
    }
  catch e =>
    throw s!"package entry '{name}': {e}"

instance : FromJson PackageEntry := ⟨PackageEntry.fromJson?⟩

@[inline] def setInherited (entry : PackageEntry) : PackageEntry :=
  {entry with inherited := true}

@[inline] def setManifestFile (path? : Option FilePath) (entry : PackageEntry) : PackageEntry :=
  {entry with manifestFile? := path?}

@[inline] def inDirectory (pkgDir : FilePath) (entry : PackageEntry) : PackageEntry :=
  {entry with source := match entry.source with | .path dir => .path (pkgDir / dir) | s => s}

def ofV6 : PackageEntryV6 → PackageEntry
| .path name _opts inherited dir =>
  let fullName := name.toString false
  {name := SimpleName.mk fullName, fullName, inherited,
    source := .path dir}
| .git name _opts inherited url rev inputRev? subDir? =>
  let fullName := name.toString false
  {name := SimpleName.mk fullName, fullName, inherited,
    source := .git url rev inputRev? subDir?}

end PackageEntry

/-- Manifest data structure that is serialized to the file. -/
structure Manifest where
  name : String
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
    ("packages", toJson self.packages),
  ]

instance : ToJson Manifest := ⟨Manifest.toJson⟩

protected def fromJson? (json : Json) : Except String Manifest := do
  try
    let obj ← JsonObject.fromJson? json
    let ver : Json ← obj.get "version"
    let .ok ver := ver.getNat?
      | throw s!"unknown version '{ver}'"
    if ver < 5 then
      throw s!"incompatible version '{ver}'"
    else if ver > Manifest.version then
      throw <|
        s!"version `{ver}` is higher than this Lake's '{Manifest.version}'; " ++
        "you may need to update your `lean-toolchain`"
    else
      let name ←
        if ver ≤ 7 then
          if let some (name : Name) ← obj.get? "name" then
            pure <| name.toString (escape := false)
          else
            pure ""
        else
          obj.getD "name" ""
      let lakeDir ← obj.getD "lakeDir" defaultLakeDir
      let packagesDir? ← obj.get? "packagesDir"
      let packages ←
        if ver ≤ 6 then
          pure <| (← obj.getD "packages" #[]).map PackageEntry.ofV6
        else
          obj.getD "packages" #[]
      return {name, lakeDir, packagesDir?, packages}
  catch e =>
    throw s!"manifest: {e}"

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
