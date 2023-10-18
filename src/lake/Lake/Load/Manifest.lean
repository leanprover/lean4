/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner
-/
import Lake.Util.Log
import Lake.Util.Name

open System Lean

/-! # Lake Manifest
The data structure of a Lake manifest and the definitions needed
to create, modify, serialize, and deserialize it.
-/

namespace Lake

/-- Current version of the manifest format. -/
def Manifest.version : Nat := 6

/-- An entry for a package stored in the manifest. -/
inductive PackageEntry
| /--
  A local filesystem package. `dir` is relative to the package directory
  of the package containing the manifest.
  -/
  path (name : Name) (opts : NameMap String) (inherited : Bool) (dir : FilePath)
| /-- A remote Git package. -/
  git (name : Name) (opts : NameMap String) (inherited : Bool) (url : String) (rev : String)
    (inputRev? : Option String) (subDir? : Option FilePath)
deriving FromJson, ToJson, Inhabited

namespace PackageEntry

@[inline] protected def name : PackageEntry → Name
| .path name .. | .git name .. => name

@[inline] protected def opts : PackageEntry → NameMap String
| .path _ opts .. | .git _ opts .. => opts

@[inline] protected def inherited : PackageEntry → Bool
| .path _ _ inherited .. | .git _ _ inherited .. => inherited

def setInherited : PackageEntry → PackageEntry
| .path name opts _ dir => .path name opts true dir
| .git name opts _ url rev inputRev? subDir? => .git name opts true url rev inputRev? subDir?

def inDirectory (pkgDir : FilePath) : PackageEntry → PackageEntry
| .path name opts inherited dir => .path name opts inherited (pkgDir / dir)
| entry => entry

end PackageEntry

/-- Manifest data structure that is serialized to the file. -/
structure Manifest where
  name? : Option Name := none
  packagesDir? : Option FilePath := none
  packages : Array PackageEntry := #[]

namespace Manifest

def empty : Manifest := {}

@[inline] def isEmpty (self : Manifest) : Bool :=
  self.packages.isEmpty

/-- Add a package entry to the end of a manifest. -/
def addPackage (entry : PackageEntry) (self : Manifest) : Manifest :=
  {self with packages := self.packages.push entry}

instance : ForIn m Manifest PackageEntry where
  forIn self init f := self.packages.forIn init f

protected def toJson (self : Manifest) : Json :=
  Json.mkObj <| .join [
    [("version", version)],
    Json.opt "name" self.name?,
    [("packagesDir", toJson self.packagesDir?)],
    [("packages", toJson self.packages)]
  ]

instance : ToJson Manifest := ⟨Manifest.toJson⟩

protected def fromJson? (json : Json) : Except String Manifest := do
  let ver ← json.getObjVal? "version"
  let .ok ver := ver.getNat? | throw s!"unknown manifest version `{ver}`"
  if ver < 5 then
    throw s!"incompatible manifest version `{ver}`"
  else if ver ≤ 6 then
    let name? ← json.getObjValAs? _ "name"
    let packagesDir? ← do
      match json.getObjVal? "packagesDir" with
      | .ok path => fromJson? path
      | .error _ => pure none
    let packages : Array PackageEntry ← fromJson? (← json.getObjVal? "packages")
    return {name?, packagesDir?, packages}
  else
    throw <|
      s!"manifest version `{ver}` is higher than this Lake's '{Manifest.version}'; " ++
      "you may need to update your `lean-toolchain`"

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

/--
 Parse the manifest file or return an empty one.
 Warn on any IO/parse errors if the file exists.
-/
def loadOrEmpty (file : FilePath) : LogIO Manifest := do
  match (← IO.FS.readFile file |>.toBaseIO) with
  | .ok contents =>
    match inline <| Manifest.parse contents with
    | .ok a => return a
    | .error e => logWarning s!"{file}: {e}"; pure {}
  | .error (.noFileOrDirectory ..) => pure {}
  | .error e => logWarning (toString e); pure {}

/-- Save the manifest as JSON to a file. -/
def saveToFile (self : Manifest) (manifestFile : FilePath) : IO PUnit := do
  let jsonString := Json.pretty self.toJson
  IO.FS.writeFile manifestFile <| jsonString.push '\n'
