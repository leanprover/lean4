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
private def PartialBuildKey.fetchInCoreAux
  (self : PartialBuildKey) (facetless : Bool := false)
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
    if let some modName := target.eraseSuffix? PartialBuildKey.moduleTargetIndicator then
      let some mod := pkg.findTargetModule? modName
        | error s!"invalid target '{root}': module target '{modName}' not found in package '{pkg.name}'"
      return ⟨.module mod.keyName, cast (by simp) <| Job.pure mod⟩
    else
      let key := BuildKey.packageTarget pkg.name target
      if facetless then
        if let some decl := pkg.findTargetDecl? target then
          if h : decl.kind.isAnonymous then
            let job ← ( pkg.target target).fetch
            return ⟨key, cast (by simp) job⟩
          else
            let facet := decl.kind.str "default"
            let tgt := decl.mkConfigTarget pkg
            let tgt := cast (by simp [decl.target_eq_type h]) tgt
            let info := BuildInfo.facet key decl.kind tgt facet
            return ⟨key.facet facet, ← info.fetch⟩
        else
          error s!"invalid target '{root}': target not found in package '{pkg.name}'"
      else
        let job ← (pkg.target target).fetch
        return ⟨key, cast (by simp) job⟩
  | .facet target shortFacet =>
      let ⟨key, job⟩ ← PartialBuildKey.fetchInCoreAux target false
      let kind := job.kind
      if h : kind.isAnonymous then
        error s!"invalid target '{root}': targets of opaque data kinds do not support facets"
      else
        let shortFacet := if shortFacet.isAnonymous then `default else shortFacet
        have facet := kind ++ shortFacet
        let some cfg := (← getWorkspace).findFacetConfig? facet
          | error s!"invalid target '{root}': unknown facet '{facet}'"
        let job ← (job.cast h).bindM (kind := cfg.outKind) fun data =>
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

/-- **For internal use only.** -/
@[inline] def PartialBuildKey.fetchInCore
  (defaultPkg : Package) (self : PartialBuildKey)
: FetchM ((key : BuildKey) × Job (BuildData key)) :=
  fetchInCoreAux defaultPkg self self true

/--
Fetches the target specified by this key, resolving gaps as needed.

* A missing package (i.e., `Name.anoanmoyus`) is filled in with `defaultPkg`.
* Facets are qualified by the their input target's kind, and missing facets
  are replaced by their kind's `default`.
* Package targets ending in `moduleTargetIndicator` are converted to module package targets.
* Package targets for non-dynamic targets (i.e., non-`target`) produce their default facet
  rather than their configuration.
-/
@[inline] def PartialBuildKey.fetchIn (defaultPkg : Package) (self : PartialBuildKey) : FetchM OpaqueJob :=
  (·.2.toOpaque) <$> fetchInCore defaultPkg self

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
        let some cfg := (← getWorkspace).findFacetConfig? facetName
          | error s!"invalid target '{root}': unknown facet '{facetName}'"
        (job.cast h).bindM (kind := cfg.outKind) fun data =>
          fetch (.facet target kind data facetName)

@[inline] protected def BuildKey.fetch
  (self : BuildKey) [FamilyOut BuildData self α] : FetchM (Job α)
:= cast (by simp) <| fetchCore self self

protected def Target.fetchIn
  [DataKind α] (defaultPkg : Package) (self : Target α) : FetchM (Job α)
:= do
  let ⟨_, job⟩ ← self.key.fetchInCore defaultPkg
  have ⟨kind, ⟨h_anon, h_kind⟩⟩ := inferInstanceAs (DataKind α)
  if h : job.kind.name = kind then
    have h := by
      have h_job := h ▸ job.kind.wf
      rw [h_job h_anon, h_kind]
    return cast h job
  else
    let actual := if job.kind.name.isAnonymous then "unknown" else s!"'{job.kind.name}'"
    error s!"type mismtach in target '{self.key}': expected '{kind}', got {actual}"

protected def TargetArray.fetchIn
  [DataKind α] (defaultPkg : Package) (self : TargetArray α) : FetchM (Job (Array α))
:= Job.collectArray <$> self.mapM (·.fetchIn defaultPkg)
