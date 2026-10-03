/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
import Lake.Build.Infos
public import Lake.Build.Job.Monad
public import Lake.Config.Workspace
import Lake.Config.Monad
import all Lake.Build.Key

/-!
# Resolve target fetch keys

Partial keys acquire package identity and qualified facet names from the workspace.
Full keys also scope unqualified module keys before registering a facet. Both paths
construct facet information from the key used for registration. Module-key
normalization and facet-key construction have checked contracts about these actual
definitions. Workspace lookup consistency, dynamic data-family equations, build
functions and asynchronous fetch/store effects remain separate obligations; these
contracts do not establish concurrent job uniqueness.
-/

open Lean

namespace Lake

/-- The target and qualified facet shared by registration and its returned key. -/
public structure ResolvedFacetRequest where
  /-- The recursively resolved target key. -/
  target : {key : BuildKey // key.moduleKeysResolved}
  /-- The qualified facet selected from the workspace. -/
  facet : Name

/-- Build information carrying exactly this request's target and facet. -/
@[expose] public def ResolvedFacetRequest.info (request : ResolvedFacetRequest)
    (kind : Name) (data : DataType kind) : BuildInfo :=
  .facet request.target.val kind data request.facet

/-- The registration key of this request, independent of its delayed data. -/
@[expose] public def ResolvedFacetRequest.key (request : ResolvedFacetRequest) : BuildKey :=
  .facet request.target.val request.facet

/--
The information fetched by the delayed continuation has the returned registration key.

## Intent
Link key agreement to the actual request constructors used by both fetch paths.
This equality does not imply atomic fetch/create/store operations.
-/
public theorem ResolvedFacetRequest.info_key (request : ResolvedFacetRequest)
    (kind : Name) (data : DataType kind) :
    (request.info kind data).key = request.key := rfl

/-- Qualify a partial facet, using the kind's default when its short name is elided. -/
@[expose] public def qualifyPartialFacet (kind shortFacet : Name) : Name :=
  kind ++ if shortFacet.isAnonymous then `default else shortFacet

/-- Qualification uses exactly the requested kind and the short or default facet. -/
public theorem qualifyPartialFacet_eq (kind shortFacet : Name) :
    qualifyPartialFacet kind shortFacet =
      kind ++ (if shortFacet.isAnonymous then `default else shortFacet) := rfl

/--
Full-key normalization selects the package-scoped key returned by partial module fetches.

## Intent
State cross-route agreement under the exact common workspace lookup. Lookup
stability across separate fetches is a premise of applying this equality to them.
-/
public theorem resolveModuleKeys?_workspace_module (ws : Workspace) (name : Name)
    (mod : Module) (h : ws.findModule? name = some mod) :
    (BuildKey.module name).resolveModuleKeys?
        (fun name => (ws.findModule? name).map (·.pkg.keyName)) =
      some (.packageModule mod.pkg.keyName name) := by
  simp [BuildKey.resolveModuleKeys?, h]

/-- A fetched partial key carries the module scoping required by enclosing facets. -/
structure ResolvedBuildJob where
  /-- Package-scoped key returned by resolution. -/
  key : BuildKey
  /-- Every nested module key includes its package. -/
  resolved : key.moduleKeysResolved
  /-- The job associated with that key. -/
  job : Job (BuildData key)

variable (defaultPkg : Package) (root : PartialBuildKey) in
def PartialBuildKey.fetchInCoreAux
  (self : PartialBuildKey) (facetless : Bool := false)
: FetchM ResolvedBuildJob := do
  match self with
  | .module modName =>
    let some mod ← findModule? modName
      | error s!"invalid target '{root}': module '{modName}' not found in workspace"
    return ⟨.packageModule mod.pkg.keyName modName, trivial,
      cast (by simp) <| Job.pure mod⟩
  | .package pkgName =>
    let pkg ← resolveTargetPackageD pkgName
    return ⟨.package pkg.keyName, trivial, cast (by simp) <| Job.pure pkg⟩
  | .packageModule pkgName modName =>
    let pkg ← resolveTargetPackageD pkgName
    let some mod := pkg.findTargetModule? modName
      | error s!"invalid target '{root}': module target '{modName}' not found in package '{pkg.prettyName}'"
    return ⟨.packageModule pkg.keyName modName, trivial, cast (by simp) <| Job.pure mod⟩
  | .packageTarget pkgName target =>
    let pkg ← resolveTargetPackageD pkgName
    let key := BuildKey.packageTarget pkg.keyName target
    if facetless then
      if let some decl := pkg.findTargetDecl? target then
        if h : decl.kind.isAnonymous then
          let job ← ( pkg.target target).fetch
          return ⟨key, trivial, cast (by simp) job⟩
        else
          let facet := decl.kind.str "default"
          let tgt := decl.mkConfigTarget pkg
          let tgt := cast (by simp [decl.target_eq_type h]) tgt
          let info := BuildInfo.facet key decl.kind tgt facet
          return ⟨key.facet facet, trivial, ← info.fetch⟩
      else
        error s!"invalid target '{root}': target not found in package '{pkg.prettyName}'"
    else
      let job ← (pkg.target target).fetch
      return ⟨key, trivial, cast (by simp) job⟩
  | .facet target shortFacet =>
      let ⟨target, resolved, job⟩ ← PartialBuildKey.fetchInCoreAux target false
      let kind := job.kind
      if h : kind.isAnonymous then
        error s!"invalid target '{root}': targets of opaque data kinds do not support facets"
      else
        let facet := qualifyPartialFacet kind shortFacet
        let some cfg := (← getWorkspace).findFacetConfig? facet
          | error s!"invalid target '{root}': unknown facet '{facet}'"
        let request : ResolvedFacetRequest := ⟨⟨target, resolved⟩, facet⟩
        let job ← (job.cast h).bindM (kind := cfg.outKind) fun data =>
          fetch (request.info kind data)
        return ⟨request.key, resolved,
          cast (by simp [ResolvedFacetRequest.key, request]) job⟩
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

/--
**For internal use only.** Resolve a partial key and fetch its job.

## Intent
Retain the resolved registration key alongside its job for enclosing facets.
-/
@[inline] public def PartialBuildKey.fetchInCore
  (defaultPkg : Package) (self : PartialBuildKey)
: FetchM ((key : BuildKey) × Job (BuildData key)) := do
  let resolved ← fetchInCoreAux defaultPkg self self true
  return ⟨resolved.key, resolved.job⟩

/--
Fetches the target specified by this key, resolving gaps as needed.

* A missing package (i.e., `Name.anonymous`) is filled in with `defaultPkg`.
* Facets are qualified by the their input target's kind, and missing facets
  are replaced by their kind's `default`.
* Package targets ending in `moduleTargetIndicator` are converted to module package targets.
* Package targets for non-dynamic targets (i.e., non-`target`) produce their default facet
  rather than their configuration.

## Intent
Resolve command-line target syntax through the workspace before facet registration.
The asynchronous build store is not a transaction across fetch, creation and storage.
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
      let ws ← getWorkspace
      let package? := fun name => (ws.findModule? name).map (·.pkg.keyName)
      let resolved : {key : BuildKey // key.moduleKeysResolved} ←
        match hResolved : target.resolveModuleKeys? package? with
        | some key => pure ⟨key,
            BuildKey.resolveModuleKeys?_resolved package? target key hResolved⟩
        | none => error s!"invalid target '{root}': module target not found in workspace"
      let kind := job.kind
      if h : kind.isAnonymous then
        error s!"invalid target '{self}': targets of opaque data kinds do not support facets"
      else
        let some cfg := (← getWorkspace).findFacetConfig? facetName
          | error s!"invalid target '{root}': unknown facet '{facetName}'"
        let request : ResolvedFacetRequest := ⟨resolved, facetName⟩
        (job.cast h).bindM (kind := cfg.outKind) fun data =>
          fetch (request.info kind data)

@[inline] public protected def BuildKey.fetch
  (self : BuildKey) [FamilyOut BuildData self α] : FetchM (Job α)
:= cast (by simp) <| fetchCore self self

public protected def Target.fetchIn
  [DataKind α] (defaultPkg : Package) (self : Target α) : FetchM (Job α)
:= do
  let ⟨_, job⟩ ← self.key.fetchInCore defaultPkg
  have ⟨kind, ⟨h_anon, h_kind⟩⟩ := (inferInstance : DataKind α)
  if h : job.kind.name = kind then
    have h := by
      have h_job := h ▸ job.kind.wf
      rw [h_job h_anon, h_kind]
    return cast h job
  else
    let actual := if job.kind.name.isAnonymous then "unknown" else s!"'{job.kind.name}'"
    error s!"type mismatch in target '{self.key}': expected '{kind}', got {actual}"

public protected def TargetArray.fetchIn
  [DataKind α] (defaultPkg : Package) (self : TargetArray α) (traceCaption := "<targets>")
: FetchM (Job (Array α)) :=
  Job.collectArray (traceCaption := traceCaption) <$> self.mapM (·.fetchIn defaultPkg)
