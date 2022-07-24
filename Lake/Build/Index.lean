/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Roots
import Lake.Build.Topological
import Lake.Util.EStateT

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
    if h : pkg.name = config.package ∧ target = config.name then
      have h' : CustomData (pkg.name, target) = ActiveBuildTarget config.resultType := by simp [h]
      liftM <| cast (by rw [← h']) <| config.target.activate
    else
      error "target's name in the configuration does not match the name it was registered with"
  else
      error s!"could not build `{target}` of `{pkg.name}` -- target not found"
| .leanLib lib =>
  mkTargetFacetBuild LeanLib.leanFacet lib.recBuildLean
| .staticLeanLib lib =>
  mkTargetFacetBuild LeanLib.staticFacet lib.recBuildStatic
| .sharedLeanLib lib =>
  mkTargetFacetBuild LeanLib.sharedFacet lib.recBuildShared
| .leanExe exe =>
  mkTargetFacetBuild LeanExe.exeFacet exe.recBuildExe
| .staticExternLib lib =>
  mkTargetFacetBuild ExternLib.staticFacet lib.target.activate
| .sharedExternLib lib =>
  mkTargetFacetBuild ExternLib.sharedFacet do
    let staticTarget := Target.active <| ← lib.static.recBuild
    staticToLeanDynlibTarget staticTarget |>.activate

/--
Recursively build the given info using the Lake build index
and a topological / suspending scheduler.
-/
def buildIndexTop' (info : BuildInfo) : RecBuildM (BuildData info.key) :=
  buildDTop BuildData BuildInfo.key recBuildWithIndex info

/--
Recursively build the given info using the Lake build index
and a topological / suspending scheduler and return the dynamic result.
-/
@[macroInline] def buildIndexTop (info : BuildInfo)
[FamilyDef BuildData info.key α] : RecBuildM α := do
  cast (by simp) <| buildIndexTop' info

/-- Build the given Lake target using the given Lake build store. -/
@[inline] def BuildInfo.buildIn
(store : BuildStore) (self : BuildInfo) [FamilyDef BuildData self.key α] : BuildM α := do
  failOnBuildCycle <| ← EStateT.run' store <| buildIndexTop self

/-- Build the given Lake target in a fresh build store. -/
@[macroInline] def BuildInfo.build
(self : BuildInfo) [FamilyDef BuildData self.key α] : BuildM α :=
  buildIn BuildStore.empty self

export BuildInfo (build buildIn)

/-! ## Targets Using the Build Index -/

/-- An opaque target that builds the info in a fresh build store. -/
@[inline] def BuildInfo.target (self : BuildInfo)
[FamilyDef BuildData self.key (ActiveBuildTarget α)] : OpaqueTarget :=
  BuildTarget.mk' () <| self.build <&> (·.task)

/-- A smart constructor for facet configurations that generate targets. -/
@[inline] def mkFacetTargetConfig (build : ι → IndexBuildM (ActiveBuildTarget α))
[h : FamilyDef Fam facet (ActiveBuildTarget α)] : FacetConfig Fam ι facet where
  build := cast (by rw [← h.family_key_eq_type]) build
  toTarget? := fun info key_eq_type =>
    have : FamilyDef BuildData info.key (ActiveBuildTarget α) :=
      ⟨h.family_key_eq_type ▸ key_eq_type⟩
    info.target
