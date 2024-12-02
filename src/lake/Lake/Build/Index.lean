/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Executable
import Lake.Build.Topological

/-!
# The Lake Build Index

The Lake build index is the complete map of Lake build keys to
Lake build functions, which is used by Lake to build any Lake build info.

This module leverages the index to perform topologically-based recursive builds.
-/

open Lean
namespace Lake
open System (FilePath)

/--
Converts a conveniently-typed target facet build function into its
dynamically-typed equivalent.
-/
@[macro_inline] def mkTargetFacetBuild
  (facet : Name) (build : FetchM (BuildJob α))
  [h : FamilyOut TargetData facet (BuildJob α)]
: FetchM (TargetData facet) :=
  cast (by rw [← h.family_key_eq_type]) build

def ExternLib.recBuildStatic (lib : ExternLib) : FetchM (BuildJob FilePath) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:static" do
  lib.config.getJob <$> fetch (lib.pkg.target lib.staticTargetName)

def ExternLib.recBuildShared (lib : ExternLib) : FetchM (BuildJob FilePath) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:shared" do
  buildLeanSharedLibOfStatic (← lib.static.fetch) lib.linkArgs

def ExternLib.recComputeDynlib (lib : ExternLib) : FetchM (BuildJob Dynlib) := do
  withRegisterJob s!"{lib.staticTargetName.toString}:dynlib" do
  computeDynlibOfShared (← lib.shared.fetch)

/-!
## Topologically-based Recursive Build Using the Index
-/

/-- Recursive build function for anything in the Lake build index. -/
def recBuildWithIndex : (info : BuildInfo) → FetchM (BuildData info.key)
| .moduleFacet mod facet => do
  if let some config := (← getWorkspace).findModuleFacetConfig? facet then
    config.build mod
  else
    error s!"do not know how to build module facet `{facet}`"
| .packageFacet pkg facet => do
  if let some config := (← getWorkspace).findPackageFacetConfig? facet then
    config.build pkg
  else
    error s!"do not know how to build package facet `{facet}`"
| .target pkg target =>
  if let some config := pkg.findTargetConfig? target then
    config.build pkg
  else
    error s!"could not build `{target}` of `{pkg.name}` -- target not found"
| .libraryFacet lib facet => do
  if let some config := (← getWorkspace).findLibraryFacetConfig? facet then
    config.build lib
  else
    error s!"do not know how to build library facet `{facet}`"
| .leanExe exe =>
  mkTargetFacetBuild LeanExe.exeFacet exe.recBuildExe
| .staticExternLib lib =>
  mkTargetFacetBuild ExternLib.staticFacet lib.recBuildStatic
| .sharedExternLib lib =>
  mkTargetFacetBuild ExternLib.sharedFacet lib.recBuildShared
| .dynlibExternLib lib =>
  mkTargetFacetBuild ExternLib.dynlibFacet lib.recComputeDynlib

/--
Run a recursive Lake build using the Lake build index
and a topological / suspending scheduler.
-/
def FetchM.run (x : FetchM α) : RecBuildM α :=
  x (inline <| recFetchMemoize BuildInfo.key recBuildWithIndex)
