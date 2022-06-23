/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Lake.Util.EStateT
import Lean.Elab.Import
import Lake.Build.Target
import Lake.Build.Actions
import Lake.Build.Recursive
import Lake.Build.Targets
import Lake.Config.Module

open Std System
open Lean hiding SearchPath

namespace Lake

abbrev ModuleSet := RBTree Module (·.name.quickCmp ·.name)
@[inline] def ModuleSet.empty : ModuleSet := RBTree.empty

abbrev ModuleMap (α) := RBMap Module α (·.name.quickCmp ·.name)
@[inline] def ModuleMap.empty : ModuleMap α := RBMap.empty

-- # Dynamic Data

class DynamicType {α : Type u} (Δ : α → Type v) (a : α) (β : outParam $ Type v) : Prop where
  eq_dynamic_type : Δ a = β

export DynamicType (eq_dynamic_type)

@[inline] def toDynamic (a : α) [DynamicType Δ a β] (b : β) : Δ a :=
  cast eq_dynamic_type.symm b

@[inline] def ofDynamic (a : α) [DynamicType Δ a β] (b : Δ a) : β :=
  cast eq_dynamic_type b

/--
The syntax:

```lean
dynamic_data foo : Data 0 := Nat
```

Declares a new alternative for the dynamic `Data` type via the
production of an axiom `foo : Data 0 = Nat` and an instance of `DynamicType`
that uses this axiom for key `0`.
-/
scoped macro (name := dynamicDataDecl) doc?:optional(Parser.Command.docComment)
"dynamic_data " id:ident " : " dty:ident key:term " := " ty:term : command => do
  let tid := extractMacroScopes dty.getId |>.name
  if let (tid, _) :: _ ← Macro.resolveGlobalName tid then
    let app := Syntax.mkApp dty #[key]
    let axm := mkIdentFrom dty <| `_root_ ++ tid ++ id.getId
    `($[$doc?]? @[simp] axiom $axm : $app = $ty
    instance : DynamicType $dty $key $ty := ⟨$axm⟩)
  else
    Macro.throwErrorAt dty s!"unknown identifier '{tid}'"

@[inline] instance [MonadDStore κ β m] [t : DynamicType β k α] : MonadStore1 k α m where
  fetch? := cast (by rw [t.eq_dynamic_type]) <| fetch? (m := m) k
  store a := store k <| cast t.eq_dynamic_type.symm a

-- # Build Key

/-- The type of keys in the Lake build store. -/
structure BuildKey where
  package? : Option WfName
  target? : Option WfName
  facet : WfName
  deriving Inhabited, Repr, DecidableEq, Hashable

namespace BuildKey

@[inline] def hasPackage (self : BuildKey) : Bool :=
  self.package? ≠ none

@[simp] theorem hasPackage_mk : BuildKey.hasPackage ⟨some p, x, f⟩ := by
  simp [BuildKey.hasPackage]

@[inline] def package (self : BuildKey) (h : self.hasPackage) : WfName :=
  match mh:self.package? with
  | some n => n
  | none => absurd mh <| by
    unfold hasPackage at h
    exact of_decide_eq_true h

@[inline] def hasTarget (self : BuildKey) : Bool :=
  self.target? ≠ none

@[simp] theorem hasTarget_mk : BuildKey.hasTarget ⟨x, some t, f⟩ := by
  simp [BuildKey.hasTarget]

@[inline] def target (self : BuildKey) (h : self.hasTarget) : WfName :=
  match mh:self.target? with
  | some n => n
  | none => absurd mh <| by
    unfold hasTarget at h
    exact of_decide_eq_true h

@[inline] def isModuleKey (self : BuildKey) : Bool :=
  self.package? = none ∧ self.hasTarget

@[simp] theorem isModuleKey_mk : BuildKey.isModuleKey ⟨none, some m, f⟩ := by
  simp [BuildKey.isModuleKey]

@[simp] theorem not_isModuleKey_pkg : ¬BuildKey.isModuleKey ⟨some pkg, x, f⟩ := by
  simp [BuildKey.isModuleKey]

@[inline] def module (self : BuildKey) (h : self.isModuleKey) : WfName :=
  self.target <| by
    unfold isModuleKey at h
    exact of_decide_eq_true h |>.2

@[inline] def isPackageKey (self : BuildKey) : Bool :=
  self.hasPackage ∧ self.target? = none

@[simp] theorem isPackageKey_mk : BuildKey.isPackageKey ⟨some p, none, f⟩ := by
  simp [BuildKey.isPackageKey]

@[inline] def isTargetKey (self : BuildKey) : Bool :=
  self.hasPackage ∧ self.hasTarget

@[simp] theorem isTargetKey_mk : BuildKey.isTargetKey ⟨some p, some t, f⟩ := by
  simp [BuildKey.isTargetKey]

protected def toString : (self : BuildKey) → String
| ⟨some p,  none,   f⟩ => s!"@{p}:{f}"
| ⟨none,    some m, f⟩ => s!"+{m}:{f}"
| ⟨some p,  some t, f⟩ => s!"{p}/{t}:{f}"
| ⟨none,    none,   f⟩ => s!":{f}"

instance : ToString BuildKey := ⟨(·.toString)⟩

def quickCmp (k k' : BuildKey) :=
  match Option.compareWith WfName.quickCmp k.package? k'.package? with
  | .eq =>
    match Option.compareWith WfName.quickCmp k.target? k'.target? with
    | .eq => k.facet.quickCmp k'.facet
    | ord => ord
  | ord => ord

theorem eq_of_quickCmp :
{k k' : _} → quickCmp k k' = Ordering.eq → k = k' := by
  intro ⟨p, t, f⟩ ⟨p', t', f'⟩
  unfold quickCmp
  simp only []
  split
  next p_eq =>
    split
    next t_eq =>
      intro f_eq
      have p_eq := eq_of_cmp p_eq
      have t_eq := eq_of_cmp t_eq
      have f_eq := eq_of_cmp f_eq
      simp only [p_eq, t_eq, f_eq]
    next =>
      intros; contradiction
  next =>
    intros; contradiction

instance : EqOfCmp BuildKey quickCmp where
  eq_of_cmp := eq_of_quickCmp

end BuildKey

-- ## Subtypes

/-- The type of build keys for modules. -/
structure ModuleBuildKey (fixedFacet : WfName) extends BuildKey where
  is_module_key : toBuildKey.isModuleKey = true
  facet_eq_fixed : toBuildKey.facet = fixedFacet

instance : Coe (ModuleBuildKey f) BuildKey := ⟨(·.toBuildKey)⟩

@[inline] def BuildKey.toModuleKey
(self : BuildKey) (h : self.isModuleKey) : ModuleBuildKey self.facet :=
  ⟨self, h, rfl⟩

@[inline] def ModuleBuildKey.module (self : ModuleBuildKey f) : WfName :=
  self.toBuildKey.module self.is_module_key

/-- The type of build keys for packages. -/
structure PackageBuildKey (fixedFacet : WfName) extends BuildKey where
  is_package_key : toBuildKey.isPackageKey = true
  facet_eq_fixed : toBuildKey.facet = fixedFacet

instance : Coe (PackageBuildKey f) BuildKey := ⟨(·.toBuildKey)⟩

@[inline] def BuildKey.toPackageKey
(self : BuildKey) (h : self.isPackageKey) : PackageBuildKey self.facet :=
  ⟨self, h, rfl⟩

@[inline] def PackageBuildKey.package (self : PackageBuildKey f) : WfName :=
  self.toBuildKey.package <| by
    have h := self.is_package_key
    unfold BuildKey.isPackageKey at h
    exact (of_decide_eq_true h).1

-- ## Constructor Helpers

@[inline] def Module.mkBuildKey (facet : WfName) (self : Module) : ModuleBuildKey facet :=
  ⟨⟨none, self.name, facet⟩, rfl, rfl⟩

@[inline] def Package.mkBuildKey (facet : WfName) (self : Package) : PackageBuildKey facet :=
  ⟨⟨self.name, none, facet⟩, rfl, rfl⟩

-- # Build Data

/--
Build data associated with module facets in the Lake build store.
For example a transitive × direct import pair for `imports` or an
active build target for `lean.c`.

It is a dynamic type, meaning additional alternatives can be add lazily
as needed.
-/
opaque ModuleData (facet : WfName) : Type

/-- Build data associated with package facets (e.g., `extraDep`). -/
opaque PackageData (facet : WfName) : Type

/-- Build data associated with Lake targets (e.g., `extern_lib`). -/
opaque TargetData (key : BuildKey) : Type

/--
The build data associated with the given key in the Lake build store.
It is dynamic type composed of the three separate dynamic types for modules,
packages, and targets.
-/
def BuildData (key : BuildKey) :=
  if key.isModuleKey then
    ModuleData key.facet
  else if key.isPackageKey then
    PackageData key.facet
  else
    TargetData key

/-- Macro for declaring new `PackageData`. -/
scoped macro (name := packageDataDecl) doc?:optional(Parser.Command.docComment)
"package_data " id:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``PackageData
  let key := WfName.quoteFrom id <| WfName.ofName <| id.getId
  `($[$doc?]? dynamic_data $id : $dty $key := $ty)

/-- Macro for declaring new `ModuleData`. -/
scoped macro (name := moduleDataDecl) doc?:optional(Parser.Command.docComment)
"module_data " id:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``ModuleData
  let key := WfName.quoteFrom id <| WfName.ofName <| id.getId
  `($[$doc?]? dynamic_data $id : $dty $key := $ty)

/-- Lean binary build (`olean`, `ilean` files) -/
module_data lean : ActiveOpaqueTarget

/-- The `olean` file produced by `lean`  -/
module_data olean : ActiveOpaqueTarget

/-- The `ilean` file produced by `lean` -/
module_data ilean : ActiveOpaqueTarget

/-- The C file built from the Lean file via `lean` -/
module_data lean.c : ActiveFileTarget

/-- The object file built from `lean.c` -/
module_data lean.o : ActiveFileTarget

/-- Shared library for `--load-dynlib` -/
module_data lean.dynlib : ActiveFileTarget

/-- The direct × transitive imports of the Lean module. -/
module_data lean.imports : Array Module × Array Module

/-- The package's `extraDepTarget`. -/
package_data extraDep : ActiveOpaqueTarget

-- # Build Store

/-- A monad equipped with a Lake build store. -/
abbrev MonadBuildStore (m) := MonadDStore BuildKey BuildData m

instance (k : ModuleBuildKey f)
[t : DynamicType ModuleData f α] : DynamicType BuildData k α where
  eq_dynamic_type := by
    unfold BuildData
    simp [k.is_module_key, k.facet_eq_fixed, t.eq_dynamic_type]

@[inline] instance [MonadBuildStore m]
[DynamicType ModuleData f α] : MonadStore (ModuleBuildKey f) α m where
  fetch? k := fetch? k.toBuildKey
  store k a := store k.toBuildKey a

instance (k : PackageBuildKey f)
[t : DynamicType PackageData f α] : DynamicType BuildData k α where
  eq_dynamic_type := by
    unfold BuildData, BuildKey.isModuleKey
    have has_pkg := of_decide_eq_true (of_decide_eq_true k.is_package_key |>.1)
    simp [has_pkg, k.is_package_key, k.facet_eq_fixed, t.eq_dynamic_type]

@[inline] instance [MonadBuildStore m]
[DynamicType PackageData f α] : MonadStore (PackageBuildKey f) α m where
  fetch? k := fetch? k.toBuildKey
  store k a := store k.toBuildKey a

-- # Build Info

inductive BuildInfo
| module (module : Module) (facet : WfName)
| package (package : Package) (facet : WfName)
| externLib (package : Package) (externLib : ExternLibConfig)
| target (package : Package) (target : WfName) (facet : WfName)

def BuildInfo.key : (self : BuildInfo) → BuildKey
| module m f => ⟨none, m.name, f⟩
| package p f => ⟨p.name, none, f⟩
| externLib p e => ⟨p.name, WfName.ofName e.name, &`externLib⟩
| target p t f => ⟨p.name, t, f⟩

-- # Build Index

/-- A build function for a single element of the Lake build index. -/
abbrev IndexBuild (m) :=
  DBuild BuildInfo (BuildData ·.key) m

/-- A recursive build function for the Lake build index. -/
abbrev RecIndexBuild (m) :=
  DRecBuild BuildInfo (BuildData ·.key) m

@[inline] def mkModuleBuild {facet : WfName} (build : Module → IndexBuild m → m α)
[h : DynamicType ModuleData facet α] : Module → IndexBuild m → m (ModuleData facet) :=
  cast (by rw [← h.eq_dynamic_type]) build

@[inline] def recBuildModuleFacet {m : Type → Type v}
(mod : Module) (facet : WfName) [DynamicType ModuleData facet α]
(build : (info : BuildInfo) → m (BuildData info.key)) : m α :=
  let to_data := by unfold BuildData, BuildInfo.key; simp [eq_dynamic_type]
  cast to_data <| build <| BuildInfo.module mod facet

@[inline] def mkPackageBuild {facet : WfName} (build : Package → IndexBuild m → m α)
[h : DynamicType PackageData facet α] : Package → IndexBuild m → m (PackageData facet) :=
  cast (by rw [← h.eq_dynamic_type]) build

@[inline] def recBuildPackageFacet {m : Type → Type v}
(pkg : Package) (facet : WfName) [DynamicType PackageData facet α]
(build : (info : BuildInfo) → m (BuildData info.key)) : m α :=
  let to_data := by unfold BuildData, BuildInfo.key; simp [eq_dynamic_type]
  cast to_data <| build <| BuildInfo.package pkg facet

abbrev ModuleBuildMap (m : Type → Type v) :=
  DRBMap WfName (cmp := WfName.quickCmp) fun k =>
    Module → IndexBuild m → m (ModuleData k)

@[inline] def ModuleBuildMap.empty : ModuleBuildMap m := DRBMap.empty

abbrev PackageBuildMap (m : Type → Type v) :=
  DRBMap WfName (cmp := WfName.quickCmp) fun k =>
    Package → IndexBuild m → m (PackageData k)

@[inline] def PackageBuildMap.empty : PackageBuildMap m := DRBMap.empty

-- # Solo Module Targets

def Module.soloTarget (mod : Module)
(dynlibs : Array FilePath) (depTarget : BuildTarget x) (c := true) : OpaqueTarget :=
  Target.opaque <| depTarget.bindOpaqueSync fun depTrace => do
    let argTrace : BuildTrace := pureHash mod.leanArgs
    let srcTrace : BuildTrace ← computeTrace mod.leanFile
    let modTrace := (← getLeanTrace).mix <| argTrace.mix <| srcTrace.mix depTrace
    let modUpToDate ← modTrace.checkAgainstFile mod mod.traceFile
    if c then
      let cUpToDate ← modTrace.checkAgainstFile mod.cFile mod.cTraceFile
      unless modUpToDate && cUpToDate do
        compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile mod.cFile
          (← getOleanPath) mod.pkg.rootDir dynlibs mod.leanArgs (← getLean)
      modTrace.writeToFile mod.cTraceFile
    else
      unless modUpToDate do
        compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile none
          (← getOleanPath) mod.pkg.rootDir dynlibs mod.leanArgs (← getLean)
    modTrace.writeToFile mod.traceFile
    return depTrace

def Module.mkCTarget (modTarget : BuildTarget x) (self : Module) : FileTarget :=
  Target.mk self.cFile <| modTarget.bindOpaqueSync fun _ =>
    return mixTrace (← computeTrace self.cFile) (← getLeanTrace)

@[inline]
def Module.mkOTarget (cTarget : FileTarget) (self : Module) : FileTarget :=
  leanOFileTarget self.oFile cTarget self.leancArgs

@[inline]
def Module.mkDynlibTarget (linkTargets : Array FileTarget) (self : Module) : FileTarget :=
  leanSharedLibTarget self.dynlib linkTargets self.linkArgs

-- # Recursive Building

section
variable [Monad m] [MonadLiftT BuildM m] [MonadBuildStore m]

/--
Recursively build a module and its (transitive, local) imports,
optionally outputting a `.c` file as well if `c` is set to `true`.
-/
@[specialize] def Module.recBuildLeanModule (mod : Module) (c : Bool)
(recurse : IndexBuild m) : m ActiveOpaqueTarget := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let extraDepTarget ← recBuildPackageFacet mod.pkg &`extraDep recurse
  let (imports, transImports) ← recBuildModuleFacet mod &`lean.imports recurse
  let dynlibsTarget ←
    if mod.shouldPrecompile then
      ActiveTarget.collectArray
        <| ← transImports.mapM (recBuildModuleFacet · &`lean.dynlib recurse)
    else
      pure <| ActiveTarget.nil.withInfo #[]
  let importTarget ←
    if c then
      ActiveTarget.collectOpaqueArray
        <| ← imports.mapM (recBuildModuleFacet · &`lean.c recurse)
    else
      ActiveTarget.collectOpaqueArray
        <| ← imports.mapM (recBuildModuleFacet · &`lean recurse)
  let depTarget := Target.active <| ← extraDepTarget.mixOpaqueAsync
    <| ← dynlibsTarget.mixOpaqueAsync importTarget
  let modTarget ← mod.soloTarget dynlibsTarget.info depTarget c |>.activate
  store (mod.mkBuildKey &`lean) modTarget
  store (mod.mkBuildKey &`olean) modTarget
  store (mod.mkBuildKey &`ilean) modTarget
  if c then
    let cTarget ← mod.mkCTarget (Target.active modTarget) |>.activate
    store (mod.mkBuildKey &`lean.c) cTarget
    return cTarget.withoutInfo
  else
    return modTarget

/--
A module facet name to build function map that contains builders for
the initial set of Lake module facets (e.g., `lean.{imports, c, o, dynlib]`).
-/
@[specialize] def moduleBuildMap : ModuleBuildMap m :=
  have : MonadLift BuildM m := ⟨liftM⟩
  ModuleBuildMap.empty.insert
  -- Compute unique imports (direct × transitive)
  &`lean.imports (mkModuleBuild <| fun mod recurse => do
    let contents ← IO.FS.readFile mod.leanFile
    let (imports, _, _) ← Elab.parseImports contents mod.leanFile.toString
    let importSet ← imports.foldlM (init := ModuleSet.empty) fun a imp => do
      if let some mod ← findModule? imp.module then return a.insert mod else return a
    let mut imports := #[]
    let mut transImports := ModuleSet.empty
    for imp in importSet do
      let (_, impTransImports) ← recBuildModuleFacet imp &`lean.imports recurse
      for imp in impTransImports do
        transImports := transImports.insert imp
      transImports := transImports.insert imp
      imports := imports.push imp
    return (imports, transImports.toArray)
  ) |>.insert
  -- Build module (`.olean` and `.ilean`)
  &`lean (mkModuleBuild <| fun mod recurse => do
    mod.recBuildLeanModule false recurse
  ) |>.insert
  &`olean (mkModuleBuild <| fun mod recurse => do
    recBuildModuleFacet mod &`lean recurse
  ) |>.insert
  &`ilean (mkModuleBuild <| fun mod recurse => do
    recBuildModuleFacet mod &`lean recurse
  ) |>.insert
  -- Build module `.c` (and `.olean` and `.ilean`)
  &`lean.c (mkModuleBuild <| fun mod recurse => do
    mod.recBuildLeanModule true recurse <&> (·.withInfo mod.cFile)
  ) |>.insert
  -- Build module `.o`
  &`lean.o (mkModuleBuild <| fun mod recurse => do
    let cTarget ← recBuildModuleFacet mod &`lean.c recurse
    mod.mkOTarget (Target.active cTarget) |>.activate
  ) |>.insert
  -- Build shared library for `--load-dynlb`
  &`lean.dynlib (mkModuleBuild <| fun mod recurse => do
    let oTarget ← recBuildModuleFacet mod &`lean.o recurse
    let dynlibTargets ←
      if mod.shouldPrecompile then
        let (_, transImports) ← recBuildModuleFacet mod &`lean.imports recurse
        transImports.mapM fun mod => recBuildModuleFacet mod &`lean.dynlib recurse
      else
        pure #[]
    -- TODO: Link in external libraries
    -- let externLibTargets ← mod.pkg.externLibTargets.mapM (·.activate)
    -- let linkTargets := #[oTarget] ++ sharedLibTargets ++ externLibTargets |>.map Target.active
    let linkTargets := #[oTarget] ++ dynlibTargets |>.map Target.active
    mod.mkDynlibTarget linkTargets |>.activate
  )

/--
A package facet name to build function map that contains builders for
the initial set of Lake package facets (e.g., `extraDep`).
-/
@[specialize] def packageBuildMap : PackageBuildMap m :=
  have : MonadLift BuildM m := ⟨liftM⟩
  PackageBuildMap.empty.insert
  -- Build the `extraDepTarget` for the package and its transitive dependencies
  &`extraDep (mkPackageBuild <| fun pkg recurse => do
    let mut target := ActiveTarget.nil
    for dep in pkg.dependencies do
      if let some depPkg ← findPackage? dep.name then
        let extraDepTarget ← recBuildPackageFacet depPkg &`extraDep recurse
        target ← target.mixOpaqueAsync extraDepTarget
    target.mixOpaqueAsync <| ← pkg.extraDepTarget.activate
  )

/-- Recursive builder for anything in the Lake build index. -/
@[specialize] def recBuildIndex : RecIndexBuild m := fun info recurse => do
  have : MonadLift BuildM m := ⟨liftM⟩
  match info with
  | .module mod facet =>
    if let some build := moduleBuildMap.find? facet then
      build mod recurse
    else
      error s!"do not know how to build module facet `{facet}`"
  | .package pkg facet =>
    if let some build := packageBuildMap.find? facet then
      build pkg recurse
    else
      error s!"do not know how to build package facet `{facet}`"
  | _ =>
    error s!"do not know how to build `{info.key}`"

/--
Recursively build the given info using the Lake build index
and a topological / suspending scheduler.
-/
@[specialize] def buildIndexTop (info : BuildInfo) : CycleT BuildKey m (BuildData info.key) :=
  buildDTop BuildData BuildInfo.key recBuildIndex info

/--
Build the module's specified facet recursively using a topological-based
scheduler, storing the results in the monad's store and returning the result
of the top-level build.
-/
@[inline] def buildModuleTop (mod : Module) (facet : WfName)
[h : DynamicType ModuleData facet α] : CycleT BuildKey m α  :=
  have of_data := by unfold BuildData, BuildInfo.key; simp [h.eq_dynamic_type]
  cast of_data <| buildIndexTop (m := m) <| BuildInfo.module mod facet

/--
Build the module's specified facet recursively using a topological-based
scheduler, storing the results in the monad's store and returning nothing.
-/
@[inline] def buildModuleTop' (mod : Module) (facet : WfName) : CycleT BuildKey m PUnit :=
  discard <| buildIndexTop (m := m) <| BuildInfo.module mod facet

/--
Build the package's specified facet recursively using a topological-based
scheduler, storing the results in the monad's store and returning the result
of the top-level build.
-/
@[inline] def buildPackageTop (pkg : Package) (facet : WfName)
[h : DynamicType PackageData facet α] : CycleT BuildKey m α  :=
  have of_data := by unfold BuildData, BuildInfo.key; simp [h.eq_dynamic_type]
  cast of_data <| buildIndexTop (m := m) <| BuildInfo.package pkg facet

end

-- ## Build Store

abbrev BuildStore :=
  DRBMap BuildKey BuildData BuildKey.quickCmp

@[inline] def BuildStore.empty : BuildStore := DRBMap.empty

-- ## Facet Builders

/--
Recursively build the specified facet of the given package,
returning the result.
-/
def buildPackageFacet
(pkg : Package) (facet : WfName)
[DynamicType PackageData facet α] : BuildM α := do
  failOnBuildCycle <| ← EStateT.run' BuildStore.empty do
    buildPackageTop pkg facet

/--
Recursively build the specified facet of the given module,
returning the result.
-/
def buildModuleFacet
(mod : Module) (facet : WfName)
[DynamicType ModuleData facet α] : BuildM α := do
  failOnBuildCycle <| ← EStateT.run' BuildStore.empty do
    buildModuleTop mod facet

/--
Recursively build the specified facet of each module,
returning an `Array`  of the results.
-/
def buildModuleFacetArray
(mods : Array Module) (facet : WfName)
[DynamicType ModuleData facet α] : BuildM (Array α) := do
  failOnBuildCycle <| ← EStateT.run' BuildStore.empty <| mods.mapM fun mod =>
    buildModuleTop mod facet

/--
Recursively build the specified facet of the given module,
returning the resulting map of built modules and their results.
-/
def buildModuleFacetMap
(mods : Array Module) (facet : WfName)
[DynamicType ModuleData facet α] : BuildM (NameMap α) := do
  let (x, bStore) ← EStateT.run BuildStore.empty <| mods.forM fun mod =>
    buildModuleTop' mod facet
  failOnBuildCycle x
  let mut res : NameMap α := RBMap.empty
  for ⟨k, v⟩ in bStore do
    if h : k.isModuleKey ∧ k.facet = facet then
      let of_data := by
        unfold BuildData
        simp [h, eq_dynamic_type]
      res := res.insert (k.module h.1) <| cast of_data v
  return res
