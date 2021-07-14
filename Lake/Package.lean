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
  src  : Source
  args : List String := []

structure PackageConfig where
  name : String
  version : String
  leanVersion : String := leanVersionString
  leanArgs : Array String := #[]
  leancArgs : Array String := #[]
  linkArgs : Array String := #[]
  module : Name := name.capitalize
  dependencies : List Dependency := []
  deriving Inhabited

structure Package where
  dir : FilePath
  config : PackageConfig
  deriving Inhabited

def Packager := FilePath → List String → IO PackageConfig

namespace Package

def name (self : Package) : String :=
  self.config.name

def version (self : Package) : String :=
  self.config.version

def leanVersion (self : Package) : String :=
  self.config.leanVersion

def module (self : Package) : Name :=
  self.config.module

def moduleName (self : Package) : String :=
  self.config.module.toString

def dependencies (self : Package) : List Dependency :=
  self.config.dependencies

def leanArgs (self : Package) : Array String :=
  self.config.leanArgs

def leancArgs (self : Package) : Array String :=
  self.config.leancArgs

def linkArgs (self : Package) : Array String :=
  self.config.linkArgs

def sourceDir (self : Package) : FilePath :=
  self.dir

def sourceRoot (self : Package) : FilePath :=
  self.sourceDir / self.moduleName

def modToSource (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.sourceDir mod "lean"

def buildDir (self : Package) : FilePath :=
  self.dir / Lake.buildPath

def oleanDir (self : Package) : FilePath :=
  self.buildDir

def oleanRoot (self : Package) : FilePath :=
  self.oleanDir / FilePath.withExtension self.moduleName "olean"

def modToHashFile (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oleanDir mod "hash"

def modToOlean (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oleanDir mod "olean"

def tempBuildDir (self : Package) : FilePath :=
  self.dir / tempBuildPath

def cDir (self : Package) : FilePath :=
  self.tempBuildDir

def modToC (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.cDir mod "c"

def oDir (self : Package) : FilePath :=
  self.tempBuildDir

def modToO (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oDir mod "o"

def binDir (self : Package) : FilePath :=
  self.buildDir / "bin"

def binName (self : Package) : FilePath :=
  self.moduleName

def binFileName (self : Package) : FilePath :=
  FilePath.withExtension self.binName FilePath.exeExtension

def binFile (self : Package) : FilePath :=
  self.binDir / self.binFileName

def libDir (self : Package) : FilePath :=
  self.buildDir / "lib"

def staticLibName (self : Package) : FilePath :=
  self.moduleName

def staticLibFileName (self : Package) : FilePath :=
  s!"lib{self.module}.a"

def staticLibFile (self : Package) : FilePath :=
  self.libDir / self.staticLibFileName
