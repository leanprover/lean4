/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner
-/
import Lean.Data.Json
import Lake.Util.Log

open System Lean

namespace Lake

instance [ToJson α] : ToJson (NameMap α) where
  toJson m := Json.obj <| m.fold (fun n k v => n.insert compare k.toString (toJson v)) .leaf

instance [FromJson α] : FromJson (NameMap α) where
  fromJson? j := do
    (← j.getObj?).foldM (init := {}) fun m k v =>
      let k := k.toName
      if k.isAnonymous then
        throw "expected name"
      else
        return m.insert k (← fromJson? v)

/-- Current version of the manifest format. -/
def Manifest.version : Nat := 5

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

/-- Manifest file format. -/
structure Manifest where
  packagesDir? : Option FilePath := none
  entryMap : NameMap PackageEntry := {}

namespace Manifest

def empty : Manifest := {}

def isEmpty (self : Manifest) : Bool :=
  self.entryMap.isEmpty

def entryArray (self : Manifest) : Array PackageEntry :=
  self.entryMap.fold (fun a _ v => a.push v) #[]

def contains (packageName : Name) (self : Manifest) : Bool :=
  self.entryMap.contains packageName

def find? (packageName : Name) (self : Manifest) : Option PackageEntry :=
  self.entryMap.find? packageName

def insert (entry : PackageEntry) (self : Manifest) : Manifest :=
  {self with entryMap := self.entryMap.insert entry.name entry}

instance : ForIn m Manifest PackageEntry where
  forIn self init f := self.entryMap.forIn init (f ·.2)

protected def toJson (self : Manifest) : Json :=
  Json.mkObj [
    ("version", version),
    ("packagesDir", toJson self.packagesDir?),
    ("packages", toJson self.entryArray)
  ]

instance : ToJson Manifest := ⟨Manifest.toJson⟩

protected def fromJson? (json : Json) : Except String Manifest := do
  let ver ← (← json.getObjVal? "version").getNat?
  if ver = 5 then
    let packagesDir? ← do
      match json.getObjVal? "packagesDir" with
      | .ok path => fromJson? path
      | .error _ => pure none
    let entries : Array PackageEntry ← fromJson? (← json.getObjVal? "packages")
    return {
      packagesDir?,
      entryMap := entries.foldl (fun map entry => map.insert entry.name entry) {}
    }
  else if ver < 5 then
    throw s!"incompatible manifest version `{ver}`"
  else
    throw s!"unknown manifest version `{ver}`"

instance : FromJson Manifest := ⟨Manifest.fromJson?⟩

def loadFromFile (file : FilePath) : IO Manifest := do
  let contents ← IO.FS.readFile file
  match Json.parse contents with
  | .ok json =>
    match fromJson? json with
    | .ok manifest =>
      return manifest
    | .error e =>
      throw <| IO.userError <| s!"improperly formatted manifest: {e}"
  | .error e =>
    throw <| IO.userError <| s!"invalid JSON in manifest: {e}"

def loadOrEmpty (file : FilePath) : LogIO Manifest := do
  match (← loadFromFile file |>.toBaseIO) with
  | .ok a => return a
  | .error e =>
    unless e matches .noFileOrDirectory .. do
      logWarning (toString e)
    return {}

def saveToFile (self : Manifest) (manifestFile : FilePath) : IO PUnit := do
  let jsonString := Json.pretty self.toJson
  IO.FS.writeFile manifestFile <| jsonString.push '\n'
