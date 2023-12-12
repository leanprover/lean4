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

/-- Current version of the manifest format. -/
def Manifest.version : Nat := 7

/-- An entry for a package stored in the manifest. -/
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

/-- An entry for a package stored in the manifest. -/
inductive PackageEntry
  /--
  A local filesystem package. `dir` is relative to the package directory
  of the package containing the manifest.
  -/
  | path
    (name : Name)
    (inherited : Bool)
    (configFile : FilePath)
    (manifestFile? : Option FilePath)
    (dir : FilePath)
  /-- A remote Git package. -/
  | git
    (name : Name)
    (inherited : Bool)
    (configFile : FilePath)
    (manifestFile? : Option FilePath)
    (url : String)
    (rev : String)
    (inputRev? : Option String)
    (subDir? : Option FilePath)
  deriving Inhabited

namespace PackageEntry

protected def toJson : PackageEntry → Json
| .path name inherited configFile manifestFile? dir => Json.mkObj [
  ("type", "path"),
  ("inherited", toJson inherited),
  ("name", toJson name),
  ("configFile" , toJson configFile),
  ("manifestFile", toJson manifestFile?),
  ("inherited", toJson inherited),
  ("dir", toJson dir)
]
| .git name inherited configFile manifestFile? url rev inputRev? subDir? => Json.mkObj [
  ("type", "git"),
  ("inherited", toJson inherited),
  ("name", toJson name),
  ("configFile" , toJson configFile),
  ("manifestFile", toJson manifestFile?),
  ("url", toJson url),
  ("rev", toJson rev),
  ("inputRev", toJson inputRev?),
  ("subDir", toJson subDir?)
]

instance : ToJson PackageEntry := ⟨PackageEntry.toJson⟩

protected def fromJson? (json : Json) : Except String PackageEntry := do
  let obj ← json.getObj?
  let type ← get obj "type"
  let name ← get obj "name"
  let inherited ← get obj "inherited"
  let configFile ← getD obj "configFile" defaultConfigFile
  let manifestFile ← getD obj "manifestFile" defaultManifestFile
  match type with
  | "path"=>
    let dir ← get obj "dir"
    return .path name inherited configFile manifestFile dir
  | "git" =>
    let url ← get obj "url"
    let rev ← get obj "rev"
    let inputRev? ← get? obj "inputRev"
    let subDir? ← get? obj "subDir"
    return .git name inherited configFile manifestFile url rev inputRev? subDir?
  | _ =>
    throw s!"unknown package entry type '{type}'"
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

@[inline] protected def name : PackageEntry → Name
| .path (name := name) .. | .git (name := name) .. => name

@[inline] protected def inherited : PackageEntry → Bool
| .path (inherited := inherited) .. | .git (inherited := inherited) .. => inherited

def setInherited : PackageEntry → PackageEntry
| .path name _ configFile manifestFile? dir =>
  .path name true configFile manifestFile? dir
| .git name _ configFile manifestFile? url rev inputRev? subDir? =>
  .git name true configFile manifestFile? url rev inputRev? subDir?

@[inline] protected def configFile : PackageEntry → FilePath
| .path (configFile := configFile) .. | .git (configFile := configFile) .. => configFile

@[inline] protected def manifestFile? : PackageEntry →  Option FilePath
| .path (manifestFile? := manifestFile?) .. | .git (manifestFile? := manifestFile?) .. => manifestFile?

def setManifestFile (path? : Option FilePath) : PackageEntry → PackageEntry
| .path name inherited configFile _ dir =>
  .path name inherited configFile path? dir
| .git name inherited configFile _ url rev inputRev? subDir? =>
  .git name inherited configFile path? url rev inputRev? subDir?

def inDirectory (pkgDir : FilePath) : PackageEntry → PackageEntry
| .path name inherited configFile manifestFile? dir =>
  .path name inherited configFile manifestFile? (pkgDir / dir)
| entry => entry

def ofV6 : PackageEntryV6 → PackageEntry
| .path name _opts inherited dir =>
  .path name inherited defaultConfigFile none dir
| .git name _opts inherited url rev inputRev? subDir? =>
  .git name inherited defaultConfigFile none url rev inputRev? subDir?

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
    | throw s!"unknown manifest version `{ver}`"
  if ver < 5 then
    throw s!"incompatible manifest version `{ver}`"
  else if ver ≤ 6 then
    let name ← getD obj "name" Name.anonymous
    let lakeDir ← getD obj "lakeDir" defaultLakeDir
    let packagesDir? ← get? obj "packagesDir"
    let pkgs : Array PackageEntryV6 ← getD obj "packages" #[]
    return {name, lakeDir, packagesDir?, packages := pkgs.map PackageEntry.ofV6}
  else if ver = 7 then
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
  | .ok json =>
    match fromJson? json with
    | .ok manifest => return manifest
    | .error e => throw s!"improperly formatted manifest: {e}"
  | .error e => throw s!"invalid JSON: {e}"

/--
Parse the manifest file. Returns `none` if the file does not exist.
Errors if the manifest is ill-formatted or the read files for other reasons.
-/
def load? (file : FilePath) : IO (Option Manifest) := do
  match (← IO.FS.readFile file |>.toBaseIO) with
  | .ok contents =>
    match inline <| Manifest.parse contents with
    | .ok a => return some a
    | .error e => error s!"{file}: {e}"
  | .error (.noFileOrDirectory ..) => pure none
  | .error e => throw e

/-- Save the manifest as JSON to a file. -/
def saveToFile (self : Manifest) (manifestFile : FilePath) : IO PUnit := do
  let jsonString := Json.pretty self.toJson
  IO.FS.writeFile manifestFile <| jsonString.push '\n'
