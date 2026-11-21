/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
import Lake.Build.Facets
import Lake.Build.Infos
public import Lake.Build.Job.Monad
import Lake.Config.Monad
import all Lake.Build.Key

open Lean

namespace Lake

/--
Lake's own facets that build a library's or module's shared library, static library or object file,
as named in `plugins`, `dynlibs`, `moreLinkObjs` and `moreLinkLibs`.
-/
def lakeLinkFacets : Array Name := #[
  LeanLib.sharedFacet, LeanLib.staticFacet, LeanLib.staticExportFacet, Module.dynlibFacet,
  Module.oFacet, Module.oExportFacet, Module.oNoExportFacet,
  Module.coFacet, Module.coExportFacet, Module.coNoExportFacet, Module.bcoFacet]

variable (defaultPkg : Package) (root : PartialBuildKey) in
def PartialBuildKey.fetchInCoreAux
  (self : PartialBuildKey) (facetless : Bool := false) (inPlace : Bool := false)
: FetchM ((key : BuildKey) × Job (BuildData key)) := do
  match self with
  | .module modName =>
    let some mod ← findModule? modName
      | error s!"invalid target '{root}': module '{modName}' not found in workspace"
    return ⟨.packageModule mod.pkg.keyName modName, cast (by simp) <| Job.pure mod⟩
  | .package pkgName =>
    let pkg ← resolveTargetPackageD pkgName
    return ⟨.package pkg.keyName, cast (by simp) <| Job.pure pkg⟩
  | .packageModule pkgName modName =>
    let pkg ← resolveTargetPackageD pkgName
    let some mod := pkg.findTargetModule? modName
      | error s!"invalid target '{root}': module target '{modName}' not found in package '{pkg.prettyName}'"
    return ⟨.packageModule pkg.keyName modName, cast (by simp) <| Job.pure mod⟩
  | .packageTarget pkgName target =>
    let pkg ← resolveTargetPackageD pkgName
    let key := BuildKey.packageTarget pkg.keyName target
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
        error s!"invalid target '{root}': target not found in package '{pkg.prettyName}'"
    else
      let job ← (pkg.target target).fetch
      return ⟨key, cast (by simp) job⟩
  | .facet target shortFacet =>
      -- Use the resolved target for the facet's build-store key.
      let ⟨target, job⟩ ← PartialBuildKey.fetchInCoreAux target false inPlace
      let kind := job.kind
      if h : kind.isAnonymous then
        error s!"invalid target '{root}': targets of opaque data kinds do not support facets"
      else
        let shortFacet := if shortFacet.isAnonymous then `default else shortFacet
        have facet := kind ++ shortFacet
        let some cfg := (← getWorkspace).findFacetConfig? facet
          | error s!"invalid target '{root}': unknown facet '{facet}'"
        -- On a finished job, a `sync` bind runs its continuation before returning.
        let sync ←
          if inPlace && lakeLinkFacets.contains facet then IO.hasFinished job.task else pure false
        let job ← (job.cast h).bindM (sync := sync) (kind := cfg.outKind) fun data =>
          fetch (.facet target kind data facet)
        return ⟨.facet target facet, cast (by simp) job⟩
where
  @[inline] resolveTargetPackageD  (name : Name) : FetchM Package := do
    match name with
    | .anonymous =>
      return defaultPkg
    | p@(.num ..) =>
      let some pkg ← findPackageByKey? p
        | error s!"invalid target '{root}': package '{name}' not found in workspace"
      return pkg
    | p =>
      let some pkg ← findPackageByName? p
        | error s!"invalid target '{root}': package '{name}' not found in workspace"
      return pkg

/-- **For internal use only.** -/
@[inline] public def PartialBuildKey.fetchInCore
  (defaultPkg : Package) (self : PartialBuildKey)
: FetchM ((key : BuildKey) × Job (BuildData key)) :=
  fetchInCoreAux defaultPkg self self true

/--
Fetches the target specified by this key, resolving gaps as needed.

* A missing package (i.e., `Name.anonymous`) is filled in with `defaultPkg`.
* Facets are qualified by the their input target's kind, and missing facets
  are replaced by their kind's `default`.
* Package targets ending in `moduleTargetIndicator` are converted to module package targets.
* Package targets for non-dynamic targets (i.e., non-`target`) produce their default facet
  rather than their configuration.
-/
@[inline] public def PartialBuildKey.fetchIn (defaultPkg : Package) (self : PartialBuildKey) : FetchM OpaqueJob :=
  (·.2.toOpaque) <$> fetchInCore defaultPkg self

variable (root : BuildKey) in
def BuildKey.fetchCore
  (self : BuildKey)
: FetchM (Job (BuildData self)) :=
  match self with
  | module modName => do
    let some mod ← findModule? modName
      | error s!"invalid target '{root}': module '{modName}' not found in workspace"
    return cast (by simp) <| Job.pure mod
  | package pkgName => do
    let some pkg ← findPackageByKey? pkgName
      | error s!"invalid target '{root}': package '{pkgName}' not found in workspace"
    return cast (by simp) <| Job.pure pkg.toPackage
  | packageModule pkgName modName => do
    let some pkg ← findPackageByKey? pkgName
      | error s!"invalid target '{root}': package '{pkgName}' not found in workspace"
    let some mod := pkg.findTargetModule? modName
      | error s!"invalid target '{root}': module '{modName}' not found in package '{pkg.prettyName}'"
    return cast (by simp) <| Job.pure mod
  | packageTarget pkgName target => do
    let some pkg ← findPackageByKey? pkgName
      | error s!"invalid target '{root}': package '{pkgName}' not found in workspace"
    fetch <| pkg.target target
  | facet target facetName => do
      let job ← target.fetchCore
      let kind := job.kind
      if h : kind.isAnonymous then
        error s!"invalid target '{self}': targets of opaque data kinds do not support facets"
      else
        let some cfg := (← getWorkspace).findFacetConfig? facetName
          | error s!"invalid target '{root}': unknown facet '{facetName}'"
        (job.cast h).bindM (kind := cfg.outKind) fun data =>
          fetch (.facet target kind data facetName)

@[inline] public protected def BuildKey.fetch
  (self : BuildKey) [FamilyOut BuildData self α] : FetchM (Job α)
:= cast (by simp) <| fetchCore self self

def Target.fetchInAux
  [DataKind α] (defaultPkg : Package) (self : Target α) (inPlace : Bool) : FetchM (Job α)
:= do
  let ⟨_, job⟩ ← self.key.fetchInCoreAux defaultPkg self.key true inPlace
  have ⟨kind, ⟨h_anon, h_kind⟩⟩ := (inferInstance : DataKind α)
  if h : job.kind.name = kind then
    have h := by
      have h_job := h ▸ job.kind.wf
      rw [h_job h_anon, h_kind]
    return cast h job
  else
    let actual := if job.kind.name.isAnonymous then "unknown" else s!"'{job.kind.name}'"
    error s!"type mismatch in target '{self.key}': expected '{kind}', got {actual}"

public protected def Target.fetchIn
  [DataKind α] (defaultPkg : Package) (self : Target α) : FetchM (Job α)
:= self.fetchInAux defaultPkg false

/--
**For internal use only.**
Like `Target.fetchIn`, but if the key names one of Lake's own facets of a library or module that
build a shared library, static library or object file (e.g., `Plug:shared`), and the job of the
facet's target has finished, as the job of a module, a package or a configured target always has,
the facet is fetched before this returns rather than in a continuation that runs later. If the
facet is memoized and its fetch function returns a job, even a failed one, a later fetch of the key
then finds that job instead of possibly creating another (#15435). Other facets, such as a
package's own facets, are fetched as by `Target.fetchIn`.

The facet's fetch function can block, so this must not run where blocking is not allowed, such as
in a `(sync := true)` task. Lake uses it only in fetch functions that can already block on a
module's imports, such as `Module.recFetchPreSetup`.
-/
public protected def Target.fetchInBlocking
  [DataKind α] (defaultPkg : Package) (self : Target α) : FetchM (Job α)
:= self.fetchInAux defaultPkg true

public protected def TargetArray.fetchIn
  [DataKind α] (defaultPkg : Package) (self : TargetArray α) (traceCaption := "<targets>")
: FetchM (Job (Array α)) :=
  Job.collectArray (traceCaption := traceCaption) <$> self.mapM (·.fetchIn defaultPkg)

/-- **For internal use only.** Like `TargetArray.fetchIn`, but uses `Target.fetchInBlocking`. -/
public protected def TargetArray.fetchInBlocking
  [DataKind α] (defaultPkg : Package) (self : TargetArray α) (traceCaption := "<targets>")
: FetchM (Job (Array α)) :=
  Job.collectArray (traceCaption := traceCaption) <$> self.mapM (·.fetchInBlocking defaultPkg)
