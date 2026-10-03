/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
import Lake.Build.Infos
public import Lake.Build.Job.Monad
import Lake.Config.Workspace
import Lake.Config.Monad
import all Lake.Build.Key

/-!
# Resolve target fetch keys

Partial keys acquire package identity and qualified facet names from the workspace.
Full keys also scope unqualified module keys before registering a facet. Both paths
construct facet information from the key used for registration, and a partial fetch
returns that key with its job so that an enclosing facet registers under it.
Module-key normalization and facet-key construction have checked contracts about
these actual definitions. Partial fetches retain their original request's successful
lookups in one captured workspace. Dynamic data-family equations, build functions and
asynchronous fetch/store effects remain separate obligations: the build store is not
a transaction across fetch, creation and storage, and these contracts do not
establish concurrent job uniqueness.
-/

open Lean

namespace Lake

/--
The target and qualified facet shared by registration and its returned key.

## Intent
Prevent an unscoped module key from reaching either facet-request constructor.
Workspace membership is established by resolution, rather than by this shape alone.
-/
structure ResolvedFacetRequest where
  /-- The recursively resolved target key. -/
  target : {key : BuildKey // key.moduleKeysResolved}
  /-- The qualified facet selected from the workspace. -/
  facet : Name

/--
Build information carrying exactly this request's target and facet.

## Intent
Use the same target and facet as `ResolvedFacetRequest.key` in the actual fetch.
-/
def ResolvedFacetRequest.info (request : ResolvedFacetRequest)
    (kind : Name) (data : DataType kind) : BuildInfo :=
  .facet request.target.val kind data request.facet

/--
The registration key of this request, independent of its delayed data.

## Intent
Retain the fetched information's key while its target job completes asynchronously.
-/
def ResolvedFacetRequest.key (request : ResolvedFacetRequest) : BuildKey :=
  .facet request.target.val request.facet

/--
The information fetched by the delayed continuation has the returned registration key.

## Intent
Link key agreement to the actual request constructors used by both fetch paths.
-/
theorem ResolvedFacetRequest.info_key (request : ResolvedFacetRequest)
    (kind : Name) (data : DataType kind) :
    (request.info kind data).key = request.key := rfl

/--
Qualify a partial facet, using the kind's default when its short name is elided.

## Intent
Derive the registration name from the actual input job's kind and requested facet.
-/
def qualifyPartialFacet (kind shortFacet : Name) : Name :=
  kind ++ if shortFacet.isAnonymous then `default else shortFacet

/--
The key of the package that owns the named module in the workspace.

## Intent
Name the one module lookup shared by full-key normalization and its contract.
-/
def Workspace.findModulePackageKey? (ws : Workspace) (name : Name) : Option Name :=
  (ws.findModule? name).map (·.pkg.keyName)

/--
Resolve a requested package against one captured workspace.

## Intent
Use the default package for an elided name, and distinguish unique keys from base names.
-/
def PartialBuildKey.resolvePackage?
    (ws : Workspace) (defaultPkg : Package) (name : Name) : Option Package :=
  match name with
  | .anonymous => some defaultPkg
  | p@(.num ..) => (ws.findPackageByKey? p).map (·.toPackage)
  | p => ws.findPackageByName? p

/--
Successful partial-key resolution in a fixed workspace, indexed by the observed job kind.

## Intent
Connect the original request to its returned key through the actual successful lookups.
Leaf kinds describe the returned job's interface; this relation does not prove its task's
result. Facet qualification uses that observed input kind and the selected output kind.
-/
inductive PartialKeyResolves (ws : Workspace) (defaultPkg : Package) :
    PartialBuildKey → Bool → BuildKey → Name → Prop where
  /-- An unscoped module uses the package of its successful workspace lookup. -/
  | module (name : Name) (mod : Module) (facetless : Bool) (kind : Name)
      (lookup : ws.findModule? name = some mod) :
      PartialKeyResolves ws defaultPkg (.module name) facetless
        (.packageModule mod.pkg.keyName name) kind
  /-- A package uses its resolved unique key. -/
  | package (name : Name) (pkg : Package) (facetless : Bool) (kind : Name)
      (lookup : PartialBuildKey.resolvePackage? ws defaultPkg name = some pkg) :
      PartialKeyResolves ws defaultPkg (.package name) facetless (.package pkg.keyName) kind
  /-- A package module must occur in the resolved package's target lookup. -/
  | packageModule (pkgName name : Name) (pkg : Package) (mod : Module)
      (facetless : Bool) (kind : Name)
      (packageLookup : PartialBuildKey.resolvePackage? ws defaultPkg pkgName = some pkg)
      (moduleLookup : pkg.findTargetModule? name = some mod) :
      PartialKeyResolves ws defaultPkg (.packageModule pkgName name) facetless
        (.packageModule pkg.keyName name) kind
  /-- An enclosing facet fetches the package target's configuration job. -/
  | packageTarget (pkgName name : Name) (pkg : Package) (kind : Name)
      (lookup : PartialBuildKey.resolvePackage? ws defaultPkg pkgName = some pkg) :
      PartialKeyResolves ws defaultPkg (.packageTarget pkgName name) false
        (.packageTarget pkg.keyName name) kind
  /-- A facetless opaque target retains its package-target key. -/
  | opaqueTarget (pkgName name : Name) (pkg : Package) (decl : NConfigDecl pkg.keyName name)
      (kind : Name)
      (packageLookup : PartialBuildKey.resolvePackage? ws defaultPkg pkgName = some pkg)
      (targetLookup : pkg.findTargetDecl? name = some decl) (opaqueKind : decl.kind.isAnonymous) :
      PartialKeyResolves ws defaultPkg (.packageTarget pkgName name) true
        (.packageTarget pkg.keyName name) kind
  /-- A facetless typed configuration target selects its kind's default facet. -/
  | defaultTarget (pkgName name : Name) (pkg : Package) (decl : NConfigDecl pkg.keyName name)
      (kind : Name)
      (packageLookup : PartialBuildKey.resolvePackage? ws defaultPkg pkgName = some pkg)
      (targetLookup : pkg.findTargetDecl? name = some decl) (typedKind : ¬ decl.kind.isAnonymous) :
      PartialKeyResolves ws defaultPkg (.packageTarget pkgName name) true
        (.facet (.packageTarget pkg.keyName name) (decl.kind.str "default")) kind
  /-- A facet derives its target and qualification from the recursively returned job. -/
  | facet (target : PartialBuildKey) (shortFacet : Name) (facetless : Bool)
      (key : BuildKey) (kind : Name) (cfg : FacetConfig (qualifyPartialFacet kind shortFacet))
      (targetResolution : PartialKeyResolves ws defaultPkg target false key kind)
      (typedKind : ¬ kind.isAnonymous)
      (facetLookup : ws.findFacetConfig? (qualifyPartialFacet kind shortFacet) = some cfg) :
      PartialKeyResolves ws defaultPkg (.facet target shortFacet) facetless
        (.facet key (qualifyPartialFacet kind shortFacet)) cfg.outKind.name

/--
Every successful partial-key resolution scopes all nested module keys.

## Intent
Derive key shape from the stronger request-to-result relation carried by actual fetches.
-/
theorem PartialKeyResolves.moduleKeysResolved
    (ws : Workspace) (defaultPkg : Package) (input : PartialBuildKey) (facetless : Bool)
    (key : BuildKey) (kind : Name)
    (resolution : PartialKeyResolves ws defaultPkg input facetless key kind) :
    key.moduleKeysResolved := by
  induction resolution <;> first | trivial | assumption

/--
Full-key normalization of an unscoped module key selects the key returned by a
successful partial resolution of that module.

## Intent
State cross-route agreement over the relation and lookup that the two fetch paths
use in one workspace. Lookup stability across separate fetches is a premise of
applying this equality to them.
-/
theorem PartialKeyResolves.resolveModuleKeys?_module
    (ws : Workspace) (defaultPkg : Package) (name : Name) (facetless : Bool)
    (key : BuildKey) (kind : Name)
    (resolution : PartialKeyResolves ws defaultPkg (.module name) facetless key kind) :
    (BuildKey.module name).resolveModuleKeys? ws.findModulePackageKey? = some key := by
  cases resolution with
  | module _ _ _ _ lookup =>
    simp [BuildKey.resolveModuleKeys?, Workspace.findModulePackageKey?, lookup]

/-- A returned job retains the resolution of its original request in the captured workspace. -/
structure ResolvedBuildJob (ws : Workspace) (defaultPkg : Package)
    (input : PartialBuildKey) (facetless : Bool) where
  /-- Package-scoped key returned by resolution. -/
  key : BuildKey
  /-- The job associated with that key. -/
  job : Job (BuildData key)
  /-- The actual returned job kind indexes the request-to-key evidence. -/
  resolution : PartialKeyResolves ws defaultPkg input facetless key job.kind.name

/-- Retain a successful lookup equation, or report the original target error. -/
@[inline] private def lookupOrError {α : Type} (lookup : Option α) (message : Unit → String) :
    FetchM {value : α // lookup = some value} :=
  match _h : lookup with
  | some value => pure ⟨value, rfl⟩
  | none => error (message ())

def PartialBuildKey.fetchInCoreAux
  (ws : Workspace) (defaultPkg : Package) (root : PartialBuildKey)
  (self : PartialBuildKey) (facetless : Bool := false)
: FetchM (ResolvedBuildJob ws defaultPkg self facetless) :=
  match self with
  | .module modName => do
    let ⟨mod, lookup⟩ ← lookupOrError (ws.findModule? modName) fun _ =>
      s!"invalid target '{root}': module '{modName}' not found in workspace"
    let job := cast (by simp) <| Job.pure mod
    return ⟨.packageModule mod.pkg.keyName modName, job, .module _ _ _ _ lookup⟩
  | .package pkgName => do
    let ⟨pkg, lookup⟩ ← lookupOrError (resolvePackage? ws defaultPkg pkgName) fun _ =>
      s!"invalid target '{root}': package '{pkgName}' not found in workspace"
    let job := cast (by simp) <| Job.pure pkg
    return ⟨.package pkg.keyName, job, .package _ _ _ _ lookup⟩
  | .packageModule pkgName modName => do
    let ⟨pkg, packageLookup⟩ ← lookupOrError (resolvePackage? ws defaultPkg pkgName) fun _ =>
      s!"invalid target '{root}': package '{pkgName}' not found in workspace"
    let ⟨mod, moduleLookup⟩ ← lookupOrError (pkg.findTargetModule? modName) fun _ =>
      s!"invalid target '{root}': module target '{modName}' not found in package '{pkg.prettyName}'"
    let job := cast (by simp) <| Job.pure mod
    return ⟨.packageModule pkg.keyName modName, job,
      .packageModule _ _ _ _ _ _ packageLookup moduleLookup⟩
  | .packageTarget pkgName target => do
    let ⟨pkg, packageLookup⟩ ← lookupOrError (resolvePackage? ws defaultPkg pkgName) fun _ =>
      s!"invalid target '{root}': package '{pkgName}' not found in workspace"
    let key := BuildKey.packageTarget pkg.keyName target
    if hFacetless : facetless then
      let ⟨decl, targetLookup⟩ ← lookupOrError (pkg.findTargetDecl? target) fun _ =>
        s!"invalid target '{root}': target not found in package '{pkg.prettyName}'"
      if h : decl.kind.isAnonymous then
        let job ← (pkg.target target).fetch
        let job := cast (by simp) job
        return ⟨key, job, hFacetless ▸ .opaqueTarget _ _ _ _ _ packageLookup targetLookup h⟩
      else
        let tgt := decl.mkConfigTarget pkg
        let tgt := cast (by simp [decl.target_eq_type h]) tgt
        let request : ResolvedFacetRequest := ⟨⟨key, trivial⟩, decl.kind.str "default"⟩
        let job ← (request.info decl.kind tgt).fetch
        return ⟨request.key, job,
          hFacetless ▸ .defaultTarget _ _ _ _ _ packageLookup targetLookup h⟩
    else
      let job ← (pkg.target target).fetch
      have hFacetless : facetless = false := Bool.eq_false_iff.mpr hFacetless
      let job := cast (by simp) job
      return ⟨key, job, by
        simpa only [hFacetless] using
          (PartialKeyResolves.packageTarget pkgName target pkg job.kind.name packageLookup)⟩
  | .facet target shortFacet => do
      let child ← PartialBuildKey.fetchInCoreAux ws defaultPkg root target false
      let target := child.key
      let job := child.job
      have resolved := child.resolution.moduleKeysResolved ws defaultPkg _ _ _ _
      let kind := job.kind
      if h : kind.isAnonymous then
        error s!"invalid target '{root}': targets of opaque data kinds do not support facets"
      else
        let facet := qualifyPartialFacet kind shortFacet
        let ⟨cfg, facetLookup⟩ ← lookupOrError (ws.findFacetConfig? facet) fun _ =>
          s!"invalid target '{root}': unknown facet '{facet}'"
        let request : ResolvedFacetRequest := ⟨⟨target, resolved⟩, facet⟩
        let job : Job (BuildData request.key) ← (job.cast h).bindM (kind := cfg.outKind) fun data =>
          fetch (request.info kind data)
        return ⟨request.key, {job with kind := cfg.outKind},
          .facet _ _ _ _ _ _ child.resolution
            (by simpa only [OptDataKind.isAnonymous_iff_name_isAnonymous] using h) facetLookup⟩

/--
**For internal use only.**
Resolves this partial key in the workspace and fetches the job of the resolved target.

## Intent
Return the job together with the full key of the target it resolved to. A missing
package is `defaultPkg`. It is an error if the workspace lacks the package, module,
target or facet, or if a facet is requested of a target with an opaque data kind.
-/
@[inline] public def PartialBuildKey.fetchInCore
  (defaultPkg : Package) (self : PartialBuildKey)
: FetchM ((key : BuildKey) × Job (BuildData key)) := do
  let ws ← getWorkspace
  let resolved ← fetchInCoreAux ws defaultPkg self self true
  return ⟨resolved.key, resolved.job⟩

/--
Fetches the target specified by this key, resolving gaps as needed.

* A missing package (i.e., `Name.anonymous`) is filled in with `defaultPkg`.
* Facets are qualified by their input target's kind, and missing facets
  are replaced by their kind's `default`.
* Package modules must be found as targets in their resolved package.
* Package targets for non-dynamic targets (i.e., non-`target`) produce their default facet
  rather than their configuration.

## Intent
Accept a target key written in configuration or on the command line and return the
job of the target it resolves to. Each facet is requested by its target's resolved
full key and its qualified facet name. It is an error if the workspace lacks the
package, module, target or facet, or if a facet is requested of a target with an
opaque data kind.
-/
@[inline] public def PartialBuildKey.fetchIn (defaultPkg : Package) (self : PartialBuildKey) : FetchM OpaqueJob :=
  (·.2.toOpaque) <$> fetchInCore defaultPkg self

def BuildKey.fetchCore
  (ws : Workspace) (root self : BuildKey)
: FetchM (Job (BuildData self)) :=
  match self with
  | module modName => do
    let some mod := ws.findModule? modName
      | error s!"invalid target '{root}': module '{modName}' not found in workspace"
    return cast (by simp) <| Job.pure mod
  | package pkgName => do
    let some pkg := ws.findPackageByKey? pkgName
      | error s!"invalid target '{root}': package '{pkgName}' not found in workspace"
    return cast (by simp) <| Job.pure pkg.toPackage
  | packageModule pkgName modName => do
    let some pkg := ws.findPackageByKey? pkgName
      | error s!"invalid target '{root}': package '{pkgName}' not found in workspace"
    let some mod := pkg.findTargetModule? modName
      | error s!"invalid target '{root}': module '{modName}' not found in package '{pkg.prettyName}'"
    return cast (by simp) <| Job.pure mod
  | packageTarget pkgName target => do
    let some pkg := ws.findPackageByKey? pkgName
      | error s!"invalid target '{root}': package '{pkgName}' not found in workspace"
    fetch <| pkg.target target
  | facet target facetName => do
      let job ← BuildKey.fetchCore ws root target
      let resolved : {key : BuildKey // key.moduleKeysResolved} ←
        match hResolved : target.resolveModuleKeys? ws.findModulePackageKey? with
        | some key => pure ⟨key,
            BuildKey.resolveModuleKeys?_resolved ws.findModulePackageKey? target key hResolved⟩
        | none => error s!"invalid target '{root}': module target not found in workspace"
      let kind := job.kind
      if h : kind.isAnonymous then
        error s!"invalid target '{self}': targets of opaque data kinds do not support facets"
      else
        let some cfg := ws.findFacetConfig? facetName
          | error s!"invalid target '{root}': unknown facet '{facetName}'"
        let request : ResolvedFacetRequest := ⟨resolved, facetName⟩
        (job.cast h).bindM (kind := cfg.outKind) fun data =>
          fetch (request.info kind data)

/--
Fetches the target specified by this full key.

## Intent
Return a job of the key's build data type `α`. A facet of a module key that names no
package is requested by the key of the package that owns the module in the workspace.
It is an error if the workspace lacks the package, module, target or facet, or if a
facet is requested of a target with an opaque data kind.
-/
@[inline] public protected def BuildKey.fetch
  {α : Type} (self : BuildKey) [FamilyOut BuildData self α] : FetchM (Job α) := do
  let ws ← getWorkspace
  cast (by simp) <| fetchCore ws self self

/--
Fetches the target specified by this typed partial key and checks its data kind.

## Intent
Resolve the key as `PartialBuildKey.fetchIn` does, with `defaultPkg` as the missing
package, and return a job of type `α`. It is a type-mismatch error if the data kind
of the resolved job is not the kind of `α`, including when that kind is unknown.
-/
public protected def Target.fetchIn
  {α : Type} [DataKind α] (defaultPkg : Package) (self : Target α) : FetchM (Job α)
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

/--
Fetches each target in this array and collects their results into one job.

## Intent
Resolve and type-check every target as `Target.fetchIn` does and return their results
in array order. An error in any one target is an error for the whole fetch.
-/
public protected def TargetArray.fetchIn
  {α : Type} [DataKind α] (defaultPkg : Package) (self : TargetArray α) (traceCaption := "<targets>")
: FetchM (Job (Array α)) :=
  Job.collectArray (traceCaption := traceCaption) <$> self.mapM (·.fetchIn defaultPkg)
