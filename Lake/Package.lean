/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Std.Data.HashMap
import Lake.LeanVersion
import Lake.BuildTarget

open Lean Std System

namespace Lake

def defaultBuildDir : FilePath := "build"
def defaultBinDir : FilePath := "bin"
def defaultLibDir : FilePath := "lib"
def defaultOleanDir : FilePath := "lib"
def defaultIrDir : FilePath := "ir"
def defaultDepsDir : FilePath := "lean_packages"

inductive Source where
  | path (dir : FilePath) : Source
  | git (url rev : String) (branch : Option String) : Source

structure Dependency where
  name : String
  src  : Source
  dir  : FilePath := "."
  args : List String := []

abbrev Script := List String → IO PUnit

structure PackageConfig where
  name : String
  version : String
  moduleRoot : Name := name.capitalize
  leanVersion : String := leanVersionString
  leanArgs : Array String := #[]
  leancArgs : Array String := #[]
  linkArgs : Array String := #[]
  rootDir : FilePath := "."
  srcDir : FilePath := rootDir
  buildDir : FilePath := defaultBuildDir
  oleanDir : FilePath := defaultOleanDir
  irDir : FilePath := defaultIrDir
  binDir : FilePath := defaultBinDir
  binName : String := name
  libDir : FilePath := defaultLibDir
  libName : String := moduleRoot.toString (escape := false)
  depsDir : FilePath := defaultDepsDir
  dependencies : List Dependency := []
  buildMoreDepsTarget : IO (LeanTarget PUnit) := LeanTarget.nil
  scripts : HashMap String Script := HashMap.empty
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

def scripts (self : Package) : HashMap String Script :=
  self.config.scripts

def moduleRoot (self : Package) : Name :=
  self.config.moduleRoot

def moduleRootName (self : Package) : String :=
  self.config.moduleRoot.toString (escape := false)

def dependencies (self : Package) : List Dependency :=
  self.config.dependencies

def buildMoreDepsTarget (self : Package) : IO (ActiveBuildTarget LeanTrace PUnit) :=
  self.config.buildMoreDepsTarget

def leanArgs (self : Package) : Array String :=
  self.config.leanArgs

def leancArgs (self : Package) : Array String :=
  self.config.leancArgs

def linkArgs (self : Package) : Array String :=
  self.config.linkArgs

def depsDir (self : Package) : FilePath :=
  self.dir / self.config.depsDir

def rootDir (self : Package) : FilePath :=
  self.dir / self.config.rootDir

def srcDir (self : Package) : FilePath :=
  self.dir / self.config.srcDir

def modToSrc (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.srcDir mod "lean"

def srcRoot (self : Package) : FilePath :=
  self.modToSrc self.moduleRoot

def buildDir (self : Package) : FilePath :=
  self.dir / self.config.buildDir

def oleanDir (self : Package) : FilePath :=
  self.buildDir / self.config.oleanDir

def modToOlean (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oleanDir mod "olean"

def oleanRoot (self : Package) : FilePath :=
  self.modToOlean self.moduleRoot

def modToHashFile (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oleanDir mod "hash"

def irDir (self : Package) : FilePath :=
  self.buildDir / self.config.irDir

def cDir (self : Package) : FilePath :=
  self.irDir

def modToC (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.cDir mod "c"

def oDir (self : Package) : FilePath :=
  self.irDir

def modToO (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oDir mod "o"

def binDir (self : Package) : FilePath :=
  self.buildDir / self.config.binDir

def binName (self : Package) : FilePath :=
  self.config.binName

def binFileName (self : Package) : FilePath :=
  FilePath.withExtension self.binName FilePath.exeExtension

def binFile (self : Package) : FilePath :=
  self.binDir / self.binFileName

def libDir (self : Package) : FilePath :=
  self.buildDir / self.config.libDir

def staticLibName (self : Package) : FilePath :=
  self.config.libName

def staticLibFileName (self : Package) : FilePath :=
  s!"lib{self.staticLibName}.a"

def staticLibFile (self : Package) : FilePath :=
  self.libDir / self.staticLibFileName
