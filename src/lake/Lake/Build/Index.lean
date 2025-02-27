/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Executable
import Lake.Build.ExternLib
import Lake.Build.Topological

/-!
# The Lake Build Index

The Lake build index is the complete map of Lake build keys to
Lake build functions, which is used by Lake to build any Lake build info.

This module leverages the index to perform topologically-based recursive builds.
-/

open Lean (Name)
open System (FilePath)

namespace Lake

/--
Converts a conveniently-typed target facet build function into its
dynamically-typed equivalent.
-/
@[macro_inline, deprecated "Deprecated without replacement." (since := "2025-02-27")]
def mkTargetFacetBuild
  (facet : Name) (build : FetchM (Job α))
  [h : FamilyOut TargetData facet α]
: FetchM (Job (TargetData facet)) :=
  cast (by rw [← h.fam_eq]) build

@[inline] private def FacetConfig.recBuild
  [h : FamilyOut TargetData kind α]
  (self : FacetConfig kind facet) (info : α)
: FetchM (Job (FacetData kind facet)) :=
  self.fetchFn <| cast (by simp) info

/-!
## Topologically-based Recursive Build Using the Index
-/

/-- Recursive build function for anything in the Lake build index. -/
def recBuildWithIndex : (info : BuildInfo) → FetchM (Job (BuildData info.key))
| .moduleFacet mod facet => do
  if let some config := (← getWorkspace).findModuleFacetConfig? facet then
    config.recBuild mod
  else
    error s!"do not know how to fetch module facet `{facet}`"
| .packageFacet pkg facet => do
  if let some config := (← getWorkspace).findPackageFacetConfig? facet then
    config.recBuild pkg
  else
    error s!"do not know how to fetch package facet `{facet}`"
| .target pkg target =>
  if let some config := pkg.findTargetConfig? target then
    config.fetchFn pkg
  else
    error s!"could not fetch `{target}` of `{pkg.name}` -- target not found"
| .libraryFacet lib facet => do
  if let some config := (← getWorkspace).findLibraryFacetConfig? facet then
    config.recBuild lib
  else
    error s!"do not know how to fetch library facet `{facet}`"
| .leanExe exe =>
  LeanExe.exeFacetConfig.recBuild exe
| .staticExternLib lib =>
  ExternLib.staticFacetConfig.recBuild lib
| .sharedExternLib lib =>
  ExternLib.sharedFacetConfig.recBuild lib
| .dynlibExternLib lib =>
  ExternLib.dynlibFacetConfig.recBuild lib

/-- Recursive build function with memoization. -/
def recFetchWithIndex : (info : BuildInfo) → RecBuildM (Job (BuildData info.key)) :=
 inline <| recFetchMemoize (β := (Job <| BuildData ·)) BuildInfo.key recBuildWithIndex

/--
Run a recursive Lake build using the Lake build index
and a topological / suspending scheduler.
-/
@[inline] def FetchT.run (x : FetchT m α) : RecBuildT m α :=
  x recFetchWithIndex
