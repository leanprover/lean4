/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Executable
import Lake.Build.Topological

/-!
# The Lake Build Index

The Lake build index is the complete map of Lake build keys to
Lake build functions, which is used by Lake to build any Lake build info.

This module leverages the index to perform topologically-based recursive builds.
-/

open Std Lean
namespace Lake

/--
Converts a conveniently typed target facet build function into its
dynamically typed equivalent.
-/
@[macroInline] def mkTargetFacetBuild (facet : Name) (build : IndexBuildM α)
[h : FamilyDef TargetData facet α] : IndexBuildM (TargetData facet) :=
  cast (by rw [← h.family_key_eq_type]) build

/-!
## Topologically-based Recursive Build Using the Index
-/

/-- Recursive build function for anything in the Lake build index. -/
def recBuildWithIndex : (info : BuildInfo) → IndexBuildM (BuildData info.key)
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
| .customTarget pkg target =>
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
  mkTargetFacetBuild ExternLib.staticFacet lib.target.activate
| .sharedExternLib lib =>
  mkTargetFacetBuild ExternLib.sharedFacet do
    let staticTarget := Target.active <| ← lib.static.recBuild
    staticToLeanSharedLibTarget lib.name staticTarget |>.activate
| .dynlibExternLib lib =>
  mkTargetFacetBuild ExternLib.dynlibFacet do
    let sharedTarget := Target.active <| ← lib.shared.recBuild
    sharedToLeanDynlibTarget sharedTarget |>.activate

/--
Recursively build the given info using the Lake build index
and a topological / suspending scheduler.
-/
def buildIndexTop' (info : BuildInfo) : RecBuildM (BuildData info.key) :=
  buildDTop BuildData BuildInfo.key info recBuildWithIndex

/--
Recursively build the given info using the Lake build index
and a topological / suspending scheduler and return the dynamic result.
-/
@[macroInline] def buildIndexTop (info : BuildInfo)
[FamilyDef BuildData info.key α] : RecBuildM α := do
  cast (by simp) <| buildIndexTop' info

/-- Build the given Lake target in a fresh build store. -/
@[inline] def BuildInfo.build
(self : BuildInfo) [FamilyDef BuildData self.key α] : BuildM α :=
  buildIndexTop self |>.run

export BuildInfo (build)

/-! ## Targets Using the Build Index -/

/-- An opaque target that builds the info in a fresh build store. -/
@[inline] def BuildInfo.target (self : BuildInfo)
[FamilyDef BuildData self.key (BuildJob α)] : BuildTarget α :=
  Target.mk <| self.build |>.catchFailure fun _ => pure failure

/-! ### Lean Executable Builds -/

@[inline] protected def LeanExe.build (self : LeanExe) : BuildM (BuildJob FilePath) :=
  self.exe.build

@[inline] protected def LeanExe.recBuild (self : LeanExe) : IndexBuildM (BuildJob FilePath) :=
  self.exe.recBuild
