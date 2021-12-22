/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build

namespace Lake

def Package.run (script : String) (args : List String) (self : Package) : ScriptIO UInt32 :=
  if let some script := self.scripts.find? script then
    script.run args
  else do
    throw <| IO.userError s!"unknown script {script}"

def Package.clean (self : Package) : IO PUnit := do
  if (← self.buildDir.pathExists) then
    IO.FS.removeDirAll self.buildDir

open PackageFacet in
def Package.defaultTarget (self : Package) : OpaqueTarget :=
  match self.defaultFacet with
  | bin => self.binTarget.withoutInfo
  | staticLib => self.staticLibTarget.withoutInfo
  | sharedLib => self.sharedLibTarget.withoutInfo
  | oleans =>  self.oleanTarget.withoutInfo
