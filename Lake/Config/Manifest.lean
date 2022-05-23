/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Json

open Lean

namespace Lake

/-- An entry for a package in the manifest. -/
structure PackageEntry where
  name : String
  url : String
  rev : String
  deriving Inhabited, Repr, FromJson, ToJson

/-- Manifest file format. -/
structure Manifest where
  version : Nat := 1
  packages : Array PackageEntry
  deriving Inhabited, Repr, FromJson, ToJson

namespace Manifest

def toMap (self : Manifest) : NameMap PackageEntry :=
  self.packages.foldl (fun map entry => map.insert entry.name entry) {}

def fromMap (map : NameMap PackageEntry) : Manifest := {
  packages := map.fold (fun a k v => a.push v) #[]
}
