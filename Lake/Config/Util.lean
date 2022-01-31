/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build

namespace Lake

def Package.run (script : String) (args : List String) (self : Package) : ScriptM UInt32 :=
  if let some script := self.scripts.find? script then
    script.run args
  else do
    error s!"unknown script {script}"

def Package.printScriptDoc (scriptName : String) (self : Package) : IO PUnit :=
  if let some script := self.scripts.find? scriptName then
    match script.doc? with
    | some doc => IO.println doc.trim
    | none => error s!"no documentation provided for `{scriptName}`"
  else
    error s!"unknown script '{scriptName}'"

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
