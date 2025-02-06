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
  (facet : Name) (build : FetchM (Job α))
  [h : FamilyOut TargetData facet α]
: FetchM (Job (TargetData facet)) :=
  cast (by rw [← h.family_key_eq_type]) build

def ExternLib.recBuildStatic (lib : ExternLib) : FetchM (Job FilePath) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:static" do
  lib.config.getPath <$> fetch (lib.pkg.target lib.staticTargetName)

def ExternLib.recBuildShared (lib : ExternLib) : FetchM (Job FilePath) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:shared" do
  buildLeanSharedLibOfStatic (← lib.static.fetch) lib.linkArgs

def ExternLib.recComputeDynlib (lib : ExternLib) : FetchM (Job Dynlib) := do
  withRegisterJob s!"{lib.staticTargetName.toString}:dynlib" do
  computeDynlibOfShared (← lib.shared.fetch)

/-!
## Topologically-based Recursive Build Using the Index
-/

/-- Recursive build function for anything in the Lake build index. -/
def recBuildWithIndex : (info : BuildInfo) → FetchM (Job (BuildData info.key))
| .moduleFacet mod facet => do
  if let some config := (← getWorkspace).findModuleFacetConfig? facet then
    config.fetchFn mod
  else
    error s!"do not know how to fetch module facet `{facet}`"
| .packageFacet pkg facet => do
  if let some config := (← getWorkspace).findPackageFacetConfig? facet then
    config.fetchFn pkg
  else
    error s!"do not know how to fetch package facet `{facet}`"
| .target pkg target =>
  if let some config := pkg.findTargetConfig? target then
    config.fetchFn pkg
  else
    error s!"could not fetch `{target}` of `{pkg.name}` -- target not found"
| .libraryFacet lib facet => do
  if let some config := (← getWorkspace).findLibraryFacetConfig? facet then
    config.fetchFn lib
  else
    error s!"do not know how to fetch library facet `{facet}`"
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
  x <| inline <|
    recFetchMemoize (β := (Job <| BuildData ·)) BuildInfo.key recBuildWithIndex
