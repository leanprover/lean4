/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Fetch
import Lake.Config.Monad
import Lake.Build.Topological
import Lake.Util.StoreInsts

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
private def recBuildWithIndex (info : BuildInfo) : FetchM (Job (BuildData info.key)) := do
  match info with
  | .target pkg target =>
    if let some decl := pkg.findTargetDecl? target then
      if h : decl.kind.isAnonymous then
        let key := BuildKey.packageTarget pkg.keyName target
        fetchOrCreate key do (decl.targetConfig h).fetchFn pkg
      else
        let kind := ⟨decl.kind, by simp [decl.target_eq_type h]⟩
        let job := Job.pure (kind := kind) <| decl.mkConfigTarget pkg
        return cast (by simp [decl.data_eq_target h]) job
    else
      error s!"invalid target '{info}': target not found in package"
  | .facet target kind data facet =>
    if let some config := (← getWorkspace).findFacetConfig? facet then
      if h : config.kind = kind then
        let recFetch := config.fetchFn <| cast (by simp [h]) data
        if config.memoize then
          let key := BuildKey.facet target facet
          fetchOrCreate key recFetch
        else
          recFetch
      else
        error s!"invalid target '{info}': \
          input target is of kind '{kind}', but facet expects '{config.kind}'"
    else
      error s!"invalid target '{info}': unknown facet '{facet}'"

/-- Recursive build function with memoization. -/
private def recFetchWithIndex : (info : BuildInfo) → RecBuildM (Job (BuildData info.key)) :=
 inline <| recFetchAcyclic (β := (Job <| BuildData ·.key)) BuildInfo.key recBuildWithIndex

/--
Run a recursive Lake build using the Lake build index
and a topological / suspending scheduler.
-/
@[inline] public nonrec def FetchT.run (x : FetchT m α) : RecBuildT m α :=
  x.run recFetchWithIndex
