/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Json
import Lake.Util.Log

open System Lean

namespace Lake

/-- Current version of the manifest format. -/
def Manifest.version : Nat := 2

/-- An entry for a package stored in the manifest. -/
structure PersistentPackageEntry where
  name : String
  url : String
  rev : String
  inputRev? : Option String
  deriving Inhabited, Repr, FromJson, ToJson

/-- An entry for a package used when resolving dependencies. -/
structure PackageEntry extends PersistentPackageEntry where
  contributors : NameMap PersistentPackageEntry := {}
  shouldUpdate : Bool := false
  deriving Inhabited

instance : ToJson PackageEntry where
  toJson x := toJson x.toPersistentPackageEntry

instance : FromJson PackageEntry where
  fromJson? x := ({toPersistentPackageEntry := ·}) <$> fromJson? x

/-- Manifest file format. -/
structure Manifest where
  entryMap : NameMap PackageEntry

namespace Manifest

def empty : Manifest :=
  ⟨{}⟩

instance : EmptyCollection Manifest := ⟨Manifest.empty⟩

def isEmpty (self : Manifest) : Bool :=
  self.entryMap.isEmpty

def ofMap (map : NameMap PackageEntry) : Manifest :=
  ⟨map⟩

def toMap (self : Manifest) : NameMap PackageEntry :=
  self.entryMap

def ofArray (entries : Array PackageEntry) : Manifest :=
  ofMap (entries.foldl (fun map entry => map.insert entry.name entry) {})

def toArray (self : Manifest) : Array PackageEntry :=
  self.toMap.fold (fun a _ v => a.push v) #[]

def contains (packageName : Name) (self : Manifest) : Bool :=
  self.entryMap.contains packageName

def find? (packageName : Name) (self : Manifest) : Option PackageEntry :=
  self.entryMap.find? packageName

def insert (entry : PackageEntry) (self : Manifest) : Manifest :=
  ⟨self.entryMap.insert entry.name entry⟩

instance : ForIn m Manifest PackageEntry where
  forIn self init f := self.entryMap.forIn init (f ·.2)

protected def toJson (self : Manifest) : Json :=
  Json.mkObj [
    ("version", version),
    ("packages", toJson self.toArray)
  ]

instance : ToJson Manifest := ⟨Manifest.toJson⟩

protected def fromJson? (json : Json) : Except String Manifest := do
  let ver ← (← json.getObjVal? "version").getNat?
  match ver with
  | 1 | 2 =>
    return ofArray <| ← (fromJson? (← json.getObjVal? "packages"))
  | v =>
    throw s!"unknown manifest version `{v}`"

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
