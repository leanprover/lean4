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

/-- Recursive build function for anything in the Lake build index. -/
def recBuildWithIndex (info : BuildInfo) : FetchM (Job (BuildData info.key)) :=
  match info with
  | .target pkg target => do
    if let some decl := pkg.findTargetDecl? target then
      if h : decl.kind.isAnonymous then
        (decl.targetConfig h).fetchFn pkg
      else
        let kind := ⟨decl.kind, by simp [decl.target_eq_type h]⟩
        let job := Job.pure (kind := kind) <| decl.mkConfigTarget pkg
        return cast (by simp [decl.data_eq_target h]) job
    else
      error s!"invalid target '{info}': target not found in package"
  | .facet _ kind data facet => do
    if let some config := (← getWorkspace).findFacetConfig? facet then
      if h : config.kind = kind then
        config.fetchFn <| cast (by simp [h]) data
      else
        error s!"invalid target '{info}': target is of kind '{kind}', but facet expects '{config.kind}'"
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
