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

def dependencies (self : Package) :=
  self.config.dependencies

def timeout (self : Package) :=
  self.config.timeout

def sourceDir (self : Package) :=
  self.dir

def sourceRoot (self : Package) :=
  self.sourceDir / self.config.module.toString

def buildDir (self : Package) :=
  self.dir / Lake.buildPath

def buildRoot (self : Package) :=
  self.buildDir / self.config.module.toString

def oleanRoot (self : Package) :=
  self.buildRoot.withExtension "olean"

end Package
