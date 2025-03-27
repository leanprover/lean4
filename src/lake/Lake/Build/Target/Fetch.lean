/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Job
import Lake.Config.Monad

namespace Lake

private def BuildKey.fetchCore (self : BuildKey) : FetchM (Job (BuildData self)) := do
  match self with
  | module modName =>
    let some mod ← findModule? modName
      | error s!"invalid target '{self}': module '{modName}' not found in workspace"
    return Job.pure <| toFamily mod
  | package pkgName =>
    let some pkg ← findPackage? pkgName
      | error s!"invalid target '{self}': package '{pkgName}' not found in workspace"
    return Job.pure <| toFamily pkg.toPackage
  | packageTarget pkgName target =>
    let some pkg ← findPackage? pkgName
      | error s!"invalid target '{self}': package '{pkgName}' not found in workspace"
    fetch <| pkg.target target
  | facet target facetName =>
      let job ← target.fetchCore
      let kind := job.kind
      if h : kind.isAnonymous then
        error s!"invalid target '{self}': targets of opaque data kinds do not support facets"
      else
        (job.cast h).bindM fun data => fetch (.facet target kind data facetName)

@[inline] protected def BuildKey.fetch
  (self : BuildKey) [FamilyOut BuildData self α] : FetchM (Job α)
:= cast (by simp) self.fetchCore

@[inline] protected def Target.fetch (self : Target α) : FetchM (Job α) := do
 have := self.data_def; self.key.fetch

protected def TargetArray.fetch (self : TargetArray α) : FetchM (Job (Array α)) := do
  Job.collectArray <$> self.mapM (·.fetch)
