/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Monad
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
    if let some decl := pkg.findTargetDecl? target then
      if k_eq : kind = decl.kind then
        if h : decl.kind.isAnonymous then
          let cfg := decl.targetConfig h
          have h := Name.eq_anonymous_of_isAnonymous h
          cast (by rw [k_eq, h]) (cfg.fetchFn pkg)
        else
          let tgt := ConfigTarget.mk pkg target decl.config'
          have h_kind := BuildKey.packageTarget pkg.name target decl.kind |>.data_eq_of_kind h
          let tgt := cast (by simp [k_eq, h_kind, decl.wf_data h |>.2]) tgt
          return Job.pure tgt
      else
        error s!"invalid target '{info}': target is of kind '{decl.kind}', but requested as '{kind}'"
    else
      error s!"invalid target '{info}': target not found in package"
  | .facet target data facet => do
    if let some config := (← getWorkspace).findFacetConfig? facet then
      if h : config.kind = target.kind then
        config.fetchFn <| cast (by simp [h]) data
      else
        error s!"invalid target '{info}': target is of kind '{target.kind}', but facet expects '{config.kind}'"
    else
      error s!"invalid target '{info}': unknown facet '{facet}'"

/-- Recursive build function with memoization. -/
def recFetchWithIndex : (info : BuildInfo) → RecBuildM (Job (BuildData info.key)) :=
 inline <| recFetchMemoize (β := (Job <| BuildData ·)) BuildInfo.key recBuildWithIndex

/--
Run a recursive Lake build using the Lake build index
and a topological / suspending scheduler.
-/
@[inline] def FetchT.run (x : FetchT m α) : RecBuildT m α :=
  x recFetchWithIndex
