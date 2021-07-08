/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.LeanVersion

open Lean System

namespace Lake

def buildPath : FilePath := "build"
def tempBuildPath := buildPath / "temp"
def depsPath := buildPath / "deps"

inductive Source where
  | path (dir : FilePath) : Source
  | git (url rev : String) (branch : Option String) : Source

structure Dependency where
  name : String
  src : Source

structure PackageConfig where
  name : String
  version : String
  leanVersion : String := leanVersionString
  leanArgs : Array String := #[]
  leancArgs : Array String := #[]
  linkArgs : Array String := #[]
  timeout : Option Nat := none
  module : Name := name.capitalize
  dependencies : List Dependency := []
  deriving Inhabited

structure Package where
  dir : FilePath
  config : PackageConfig
  deriving Inhabited

namespace Package

def name (self : Package) :=
  self.config.name

def module (self : Package) :=
  self.config.module

def moduleName (self : Package) :=
  self.config.module.toString

def dependencies (self : Package) :=
  self.config.dependencies

def leanArgs (self : Package) :=
  self.config.leanArgs

def leancArgs (self : Package) :=
  self.config.leancArgs

def linkArgs (self : Package) :=
  self.config.linkArgs

def timeout (self : Package) :=
  self.config.timeout

def sourceDir (self : Package) :=
  self.dir

def sourceRoot (self : Package) :=
  self.sourceDir / self.moduleName

def modToSource (mod : Name) (self : Package) :=
  Lean.modToFilePath self.sourceDir mod "lean"

def buildDir (self : Package) :=
  self.dir / Lake.buildPath

def oleanDir (self : Package) :=
  self.buildDir

def oleanRoot (self : Package) :=
  self.oleanDir / FilePath.withExtension self.moduleName "olean"

def modToOlean (mod : Name) (self : Package) :=
  Lean.modToFilePath self.oleanDir mod "olean"

def tempBuildDir (self : Package) :=
  self.dir / tempBuildPath

def cDir (self : Package) :=
  self.tempBuildDir

def modToC (mod : Name) (self : Package) :=
  Lean.modToFilePath self.cDir mod "c"

def oDir (self : Package) :=
  self.tempBuildDir

def modToO (mod : Name) (self : Package) :=
  Lean.modToFilePath self.oDir mod "o"

def binDir (self : Package) :=
  self.buildDir / "bin"

def binName (self : Package) :=
  self.moduleName

def binFileName (self : Package) : FilePath :=
  FilePath.withExtension self.binName FilePath.exeExtension

def binFile (self : Package) :=
  self.binDir / self.binFileName

def libDir (self : Package) :=
  self.buildDir / "lib"

def staticLibName (self : Package) :=
  self.moduleName

def staticLibFileName (self : Package) :=
  s!"lib{self.module}.a"

def staticLibFile (self : Package) :=
  self.libDir / self.staticLibFileName
