/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

public import Lake.Config.Script
public import Lake.Config.Dependency
public import Lake.Config.PackageConfig
public import Lake.Config.FacetConfig
public import Lake.Config.TargetConfig

set_option doc.verso true

open Lean

namespace Lake

/-- The configuration defined by a Lake configuration file (e.g., {lit}`lakefile.(lean|toml)`). -/
public structure LakefileConfig where
  /-- The package deceleration of the configuration file. -/
  pkgDecl : PackageDecl
  /-- Depdency configurations in the order declared by the configuration file.  -/
  depConfigs : Array Dependency := #[]
  /-- Facet configurations in the order declared by the configuration file. -/
  facetDecls : Array FacetDecl := {}
  /-- Target configurations in the order declared by the configuration file. -/
  targetDecls : Array (PConfigDecl pkgDecl.keyName) := #[]
  /-- Name-declaration map of target configurations declared in the configuration file. -/
  targetDeclMap : DNameMap (NConfigDecl pkgDecl.keyName) :=
    targetDecls.foldl (fun m d => m.insert d.name (.mk d rfl)) {}
  /-- The names of targets declared via {lit}`@[default_target]`. -/
  defaultTargets : Array Name := #[]
  /-- Scripts declared in the configuration file. -/
  scripts : NameMap Script := {}
  /-- The names of the scripts declared via {lit}`@[default_script]`. -/
  defaultScripts : Array Script := #[]
  /-- {lit}`post_update` hooks in the order declared by the configuration file.. -/
  postUpdateHooks : Array (OpaquePostUpdateHook pkgDecl.keyName) := #[]
  /--
  The name of the configuration file's test driver.

  It is either  declared via {lit}`@[test_driver]` or derived from {lean}`PackageConfig.testDriver`.
  -/
  testDriver : String := pkgDecl.config.testDriver
  /--
  The name of the configuration file's test driver.

  It is either declared via {lit}`@[lint_driver]` or derived from {lean}`PackageConfig.lintDriver`.
  -/
  lintDriver : String := pkgDecl.config.lintDriver
