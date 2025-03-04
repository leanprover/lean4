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

/-!
## Topologically-based Recursive Build Using the Index
-/

/-- Recursive build function for anything in the Lake build index. -/
def recBuildWithIndex (info : BuildInfo) : FetchM (Job (BuildData info.key)) :=
  match info with
  | .target pkg target kind => do
    match kind with
    | .anonymous =>
      if let some config := pkg.findTargetConfig? target then
        config.fetchFn pkg
      else
        error s!"invalid target '{info}': custom target '{target}' not found in package '{pkg.name}'"
    | `leanLib =>
      let some lib := pkg.findLeanLib? target
        | error s!"invalid target '{info}': Lean library '{target}' not found in package '{pkg.name}'"
      return Job.pure <| toFamily lib
    | `leanExe =>
      let some exe := pkg.findLeanExe? target
        | error s!"invalid target '{info}': Lean executable '{target}' not found in package '{pkg.name}'"
      return Job.pure <| toFamily exe
    | `externLib =>
      let some lib := pkg.findExternLib? target
        | error s!"invalid target '{info}': external library '{target}' not found in package '{pkg.name}'"
      return Job.pure <| toFamily lib
    | _ =>
      error s!"invalid target '{info}': unknown target kind '{kind}'"
  | .facet target data facet => do
    match h:target.kind with
    | `module =>
      if let some config := (← getWorkspace).findModuleFacetConfig? facet then
        cast (by simp [h]) <| config.fetchFn <| h.ndrec data
      else
        error s!"invalid target '{info}': unknown module facet`{facet}`"
    | `package =>
      if let some config := (← getWorkspace).findPackageFacetConfig? facet then
        cast (by simp [h]) <| config.fetchFn <| h.ndrec data
      else
        error s!"invalid target '{info}': unknown package facet`{facet}`"
    | `leanLib =>
      if let some config := (← getWorkspace).findLibraryFacetConfig? facet then
        cast (by simp [h]) <| config.fetchFn <| h.ndrec data
      else
        error s!"invalid target '{info}': unknown library facet `{facet}`"
    | `leanExe =>
      let `exe := facet
        | error s!"invalid target '{info}': unknown executable facet '{facet}'"
      cast (by simp [h]) <| LeanExe.exeFacetConfig.fetchFn <| h.ndrec data
    | `externLib =>
      match facet with
      | `static =>
        cast (by simp [h]) <| ExternLib.staticFacetConfig.fetchFn <| h.ndrec data
      | `shared =>
        cast (by simp [h]) <| ExternLib.sharedFacetConfig.fetchFn <| h.ndrec data
      | `dynlib =>
        cast (by simp [h]) <| ExternLib.dynlibFacetConfig.fetchFn <| h.ndrec data
      | _ =>
        error s!"invalid target '{info}': unknown external library facet '{facet}'"
    | _ =>
      error s!"invalid target '{info}': unknown target kind '{target.kind}'"

/-- Recursive build function with memoization. -/
def recFetchWithIndex : (info : BuildInfo) → RecBuildM (Job (BuildData info.key)) :=
 inline <| recFetchMemoize (β := (Job <| BuildData ·)) BuildInfo.key recBuildWithIndex

/--
Run a recursive Lake build using the Lake build index
and a topological / suspending scheduler.
-/
@[inline] def FetchT.run (x : FetchT m α) : RecBuildT m α :=
  x recFetchWithIndex
