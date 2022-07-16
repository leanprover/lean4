/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Json

open System Lean

namespace Lake

/-- An entry for a package in the manifest. -/
structure PackageEntry where
  name : String
  url : String
  rev : String
  deriving Inhabited, Repr, FromJson, ToJson

/-- Manifest file format. -/
structure Manifest where
  map : NameMap PackageEntry

namespace Manifest

/-- Current version of the manifest format. -/
def version : Nat :=
  1

def empty : Manifest :=
  ⟨{}⟩

instance : EmptyCollection Manifest := ⟨Manifest.empty⟩

def isEmpty (self : Manifest) : Bool :=
  self.map.isEmpty

def ofMap (map : NameMap PackageEntry) : Manifest :=
  ⟨map⟩

def toMap (self : Manifest) : NameMap PackageEntry :=
  self.map

def ofArray (entries : Array PackageEntry) : Manifest :=
  ofMap (entries.foldl (fun map entry => map.insert entry.name entry) {})

def toArray (self : Manifest) : Array PackageEntry :=
  self.toMap.fold (fun a _ v => a.push v) #[]

def find? (packageName : Name) (self : Manifest) : Option PackageEntry :=
  self.map.find? packageName

def insert (entry : PackageEntry) (self : Manifest) : Manifest :=
  ⟨self.map.insert entry.name entry⟩

protected def toJson (self : Manifest) : Json :=
  Json.mkObj [
    ("version", version),
    ("packages", toJson self.toArray)
  ]

instance : ToJson Manifest := ⟨Manifest.toJson⟩

protected def fromJson? (json : Json) : Except String Manifest := do
  let ver ← (← json.getObjVal? "version").getNat?
  match ver with
  | 1 =>
    let packages : Array PackageEntry ←
      (← (← json.getObjVal? "packages").getArr?).mapM fromJson?
    return ofArray packages
  | v =>
    throw s!"unknown manifest version `{v}`"

instance : FromJson Manifest := ⟨Manifest.fromJson?⟩

def loadFromFile (manifestFile : FilePath) : IO Manifest := do
  let contents ← IO.FS.readFile manifestFile
  match Json.parse contents with
  | .ok json =>
    match fromJson? json with
    | .ok manifest =>
      return manifest
    | .error e =>
      throw <| IO.userError <| s!"improperly formatted manifest: {e}"
  | .error e =>
    throw <| IO.userError <| s!"invalid JSON in manifest: {e}"

def saveToFile (self : Manifest) (manifestFile : FilePath) : IO PUnit := do
  let jsonString := Json.pretty self.toJson
  IO.FS.writeFile manifestFile <| jsonString.push '\n'
