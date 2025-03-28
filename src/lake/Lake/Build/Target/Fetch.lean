/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Job
import Lake.Config.Monad

open Lean

namespace Lake

variable (defaultPkg : Package) (root : BuildKey) in
private def PartialBuildKey.fetchInCore
  (self : PartialBuildKey)
: FetchM ((key : BuildKey) × Job (BuildData key)) := do
  match self with
  | .module modName =>
    let some mod ← findModule? modName
      | error s!"invalid target '{root}': module '{modName}' not found in workspace"
    return ⟨.module modName, cast (by simp) <| Job.pure mod⟩
  | .package pkgName =>
    let pkg ← resolveTargetPackageD pkgName
    return ⟨.package pkg.name, cast (by simp) <| Job.pure pkg⟩
  | .packageTarget pkgName target =>
    let pkg ← resolveTargetPackageD pkgName
    let job ← (pkg.target target).fetch
    return ⟨.packageTarget pkg.name target, cast (by simp) job⟩
  | .facet target facetName =>
      let ⟨key, job⟩ ← PartialBuildKey.fetchInCore target
      let kind := job.kind
      if h : kind.isAnonymous then
        error s!"invalid target '{root}': targets of opaque data kinds do not support facets"
      else
        have facet := kind ++ facetName
        let job ← (job.cast h).bindM fun data =>
          fetch (.facet target kind data facet)
        return ⟨.facet target facet, cast (by simp) job⟩
where
  @[inline] resolveTargetPackageD  (name : Name) : FetchM Package := do
    if name.isAnonymous then
      pure defaultPkg
    else
      let some pkg ← findPackage? name
        | error s!"invalid target '{root}': package '{name}' not found in workspace"
      return pkg

/--
Fetches the target specified by this key, resolving gaps as needed.
A missing package is filled in with `defaultPkg` and facets are qualified
by the their input target's kind.
-/
@[inline] def PartialBuildKey.fetchIn (defaultPkg : Package) (self : PartialBuildKey) : FetchM OpaqueJob :=
  (·.2.toOpaque) <$> fetchInCore defaultPkg self self

variable (root : BuildKey) in
private def BuildKey.fetchCore
  (self : BuildKey)
: FetchM (Job (BuildData self)) := do
  match self with
  | module modName =>
    let some mod ← findModule? modName
      | error s!"invalid target '{root}': module '{modName}' not found in workspace"
    return cast (by simp) <| Job.pure mod
  | package pkgName =>
    let some pkg ← findPackage? pkgName
      | error s!"invalid target '{root}': package '{pkgName}' not found in workspace"
    return cast (by simp) <| Job.pure pkg.toPackage
  | packageTarget pkgName target =>
    let some pkg ← findPackage? pkgName
      | error s!"invalid target '{root}': package '{pkgName}' not found in workspace"
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
:= cast (by simp) <| fetchCore self self

@[inline] protected def Target.fetch (self : Target α) : FetchM (Job α) := do
 have := self.data_def; self.key.fetch

protected def TargetArray.fetch (self : TargetArray α) : FetchM (Job (Array α)) := do
  Job.collectArray <$> self.mapM (·.fetch)
