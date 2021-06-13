/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
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

def timeout (self : Package) :=
  self.config.timeout

def sourceDir (self : Package) :=
  self.dir

def sourceRoot (self : Package) :=
  self.sourceDir / self.moduleName

def buildDir (self : Package) :=
  self.dir / Lake.buildPath

def binDir (self : Package) :=
  self.buildDir / "bin"

def binName (self : Package) :=
  self.moduleName

def binPath (self : Package) :=
  self.binDir / FilePath.withExtension self.binName FilePath.exeExtension

def libDir (self : Package) :=
  self.buildDir / "lib"

def staticLibFile (self : Package) :=
  s!"lib{self.module}.a"

def staticLibPath (self : Package) :=
  self.libDir / self.staticLibFile

def oleanDir (self : Package) :=
  self.dir / Lake.buildPath

def oleanRoot (self : Package) :=
  self.oleanDir / FilePath.withExtension self.moduleName "olean"
