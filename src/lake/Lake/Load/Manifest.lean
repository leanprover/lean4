/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner
-/
import Lean.Data.Json
import Lake.Util.Log

open System Lean

namespace Lake

/-- Current version of the manifest format. -/
def Manifest.version : Nat := 4

/-- An entry for a package stored in the manifest. -/
inductive PackageEntry
| path (name : String) (dir : FilePath)
  -- `dir` is relative to the package directory
  -- of the package containing the manifest
| git (name : String) (url : String) (rev : String)
  (inputRev? : Option String) (subDir? : Option FilePath)
deriving FromJson, ToJson, Repr, Inhabited

@[inline] def PackageEntry.name : PackageEntry → String
| path name .. | git name .. => name

def PackageEntry.inDirectory (pkgDir : FilePath) : PackageEntry → PackageEntry
| path name dir => path name (pkgDir / dir)
| entry => entry

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
  match ver with
  | 3 | 4 =>
    let packagesDir? ← do
      match json.getObjVal? "packagesDir" with
      | .ok path => fromJson? path
      | .error _ => pure none
    let entries : Array PackageEntry ← fromJson? (← json.getObjVal? "packages")
    return {
      packagesDir?,
      entryMap := entries.foldl (fun map entry => map.insert entry.name entry) {}
    }
  | 1 | 2 =>
    throw s!"incompatible manifest version `{ver}`"
  | _ =>
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
