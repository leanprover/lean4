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

@[inline]
instance [MonadDStore κ β m] [t : DynamicType β k α] : MonadStore1 k α m where
  fetch? := cast (by rw [t.eq_dynamic_type]) <| fetch? (m := m) k
  store o := store k <| cast t.eq_dynamic_type.symm o

-- ## For Facets

opaque FacetData : WfName → Type

macro "register_facet_data " id:ident " : " ty:term : command =>
  let key := WfName.quoteFrom id <| WfName.ofName <| id.getId
  let axm := mkIdent <| ``FacetData ++ id.getId
  `(@[simp] axiom $axm : FacetData $key = $ty
  instance : DynamicType FacetData $key $ty := ⟨$axm⟩)

register_facet_data lean : ActiveOpaqueTarget
register_facet_data olean : ActiveOpaqueTarget
register_facet_data ilean : ActiveOpaqueTarget
register_facet_data lean.c : ActiveFileTarget
register_facet_data lean.o : ActiveFileTarget
register_facet_data lean.dynlib : ActiveFileTarget
register_facet_data lean.imports : Array Module × Array Module
register_facet_data lean.extraDep : ActiveOpaqueTarget

-- # Build Key

structure ModuleBuildKey where
  module : WfName
  facet : WfName
  deriving Inhabited, Repr, DecidableEq, Hashable

namespace ModuleBuildKey

def quickCmp (lhs rhs : ModuleBuildKey) :=
  match lhs.module.quickCmp rhs.module with
  | .eq => lhs.facet.quickCmp rhs.facet
  | ord => ord

theorem eq_of_quickCmp :
{k k' : _} → quickCmp k k' = Ordering.eq → k = k' := by
  intro ⟨m, f⟩ ⟨m', f'⟩
  unfold quickCmp
  split
  next mod_eq =>
    intro facet_eq
    let mod_eq := WfName.eq_of_quickCmp mod_eq
    let facet_eq := WfName.eq_of_quickCmp facet_eq
    simp only [mod_eq, facet_eq]
  next =>
    intros; contradiction

instance : EqOfCmp ModuleBuildKey quickCmp where
  eq_of_cmp := eq_of_quickCmp

protected def toString (self : ModuleBuildKey) :=
  s!"{self.module}:{self.facet}"

instance : ToString ModuleBuildKey := ⟨(·.toString)⟩

end ModuleBuildKey

-- ## Static Keys

abbrev DModuleBuildKey (facet : WfName) :=
  {k : ModuleBuildKey // k.facet = facet}

def Module.mkBuildKey (facet : WfName) (self : Module) : DModuleBuildKey facet :=
  ⟨⟨self.name, facet⟩, rfl⟩

abbrev ModuleBuildKeyData (key : ModuleBuildKey) := FacetData key.facet

@[inline]
instance [MonadDStore ModuleBuildKey ModuleBuildKeyData m]
[h : DynamicType FacetData f α] : MonadStore (DModuleBuildKey f) α m where
  fetch? k :=
    let of_data := by
      unfold ModuleBuildKeyData
      rw [k.property, h.eq_dynamic_type]
    cast of_data <| MonadDStore.fetch? (m := m) k.val
  store k o :=
    let to_data := by
      unfold ModuleBuildKeyData
      rw [k.property, h.eq_dynamic_type]
    MonadDStore.store (m := m) k.val <| cast to_data o

-- # Module Build Info

structure ModuleBuildInfo extends Module where
  facet : WfName

instance : Coe ModuleBuildInfo Module := ⟨(·.toModule)⟩

def ModuleBuildInfo.buildKey (self : ModuleBuildInfo) : DModuleBuildKey self.facet :=
  self.mkBuildKey self.facet

structure DModuleBuildInfo (facet : WfName) extends ModuleBuildInfo where
  law : toModuleBuildInfo.facet = facet

instance : Coe (DModuleBuildInfo k) ModuleBuildInfo := ⟨(·.toModuleBuildInfo)⟩

abbrev Module.mkFacetInfo (facet : WfName) (self : Module) : DModuleBuildInfo facet :=
  ⟨⟨self, facet⟩, rfl⟩

abbrev ModuleBuildData (info : ModuleBuildInfo) := FacetData info.facet

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

abbrev ModuleBuild (m) :=
  DBuild ModuleBuildInfo ModuleBuildData m

abbrev FacetBuildMap (m : Type → Type v) :=
  DRBMap WfName (cmp := WfName.quickCmp) fun k =>
    Module → ModuleBuild m → m (FacetData k)

@[inline] def FacetBuildMap.empty : FacetBuildMap m := DRBMap.empty

@[inline] def mkFacetBuild {facet : WfName} (build : Module → ModuleBuild m → m α)
[h : DynamicType FacetData facet α] : Module → ModuleBuild m → m (FacetData facet) :=
  cast (by rw [← h.eq_dynamic_type]) build

@[inline] def buildFacet {m : Type → Type v}
(mod : Module) (facet : WfName) [DynamicType FacetData facet α]
(build : (info : ModuleBuildInfo) → m (ModuleBuildData info)) : m α :=
  cast (by simp only [ModuleBuildData, eq_dynamic_type]) (build ⟨mod, facet⟩)

section
variable [Monad m] [MonadLiftT BuildM m]
  [MonadDStore ModuleBuildKey ModuleBuildKeyData m]

/--
Recursively build a module and its (transitive, local) imports,
optionally outputting a `.c` file as well if `c` is set to `true`.
-/
@[inline] def Module.recBuildLeanModule (mod : Module) (c : Bool)
(recurse : ModuleBuild m) : m ActiveOpaqueTarget := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let extraDepTarget ← buildFacet mod &`lean.extraDep recurse
  let (imports, transImports) ← buildFacet mod &`lean.imports recurse
  let dynlibsTarget ←
    if mod.shouldPrecompile then
      ActiveTarget.collectArray
        <| ← transImports.mapM (buildFacet · &`lean.dynlib recurse)
    else
      pure <| ActiveTarget.nil.withInfo #[]
  let importTarget ←
    if c then
      ActiveTarget.collectOpaqueArray
        <| ← imports.mapM (buildFacet · &`lean.c recurse)
    else
      ActiveTarget.collectOpaqueArray
        <| ← imports.mapM (buildFacet · &`lean recurse)
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
A facet name to build function map that contains builders
for the initial set of Lake module facets (i.e. `lean.{imports, c, o, dynlib]`).
-/
@[specialize] def facetBuildMap : FacetBuildMap m :=
  have : MonadLift BuildM m := ⟨liftM⟩
  FacetBuildMap.empty.insert
  -- Get extra module dependency job (i.e., for package dependencies)
  &`lean.extraDep (mkFacetBuild <| fun _  _ => do
    return ActiveTarget.opaque <| (← read).extraDepJob
  ) |>.insert
  -- Compute unique imports (direct × transitive)
  &`lean.imports (mkFacetBuild <| fun mod recurse => do
    let contents ← IO.FS.readFile mod.leanFile
    let (imports, _, _) ← Elab.parseImports contents mod.leanFile.toString
    let importSet ← imports.foldlM (init := ModuleSet.empty) fun a imp => do
      if let some mod ← findModule? imp.module then return a.insert mod else return a
    let mut imports := #[]
    let mut transImports := ModuleSet.empty
    for imp in importSet do
      let (_, impTransImports) ← buildFacet imp &`lean.imports recurse
      for imp in impTransImports do
        transImports := transImports.insert imp
      transImports := transImports.insert imp
      imports := imports.push imp
    return (imports, transImports.toArray)
  ) |>.insert
  -- Build module (`.olean` and `.ilean`)
  &`lean (mkFacetBuild <| fun mod recurse => do
    mod.recBuildLeanModule false recurse
  ) |>.insert
  &`olean (mkFacetBuild <| fun mod recurse => do
    buildFacet mod &`lean recurse
  ) |>.insert
  &`ilean (mkFacetBuild <| fun mod recurse => do
    buildFacet mod &`lean recurse
  ) |>.insert
  -- Build module `.c` (and `.olean` and `.ilean`)
  &`lean.c (mkFacetBuild <| fun mod recurse => do
    mod.recBuildLeanModule true recurse <&> (·.withInfo mod.cFile)
  ) |>.insert
  -- Build module `.o`
  &`lean.o (mkFacetBuild <| fun mod recurse => do
    let cTarget ← buildFacet mod &`lean.c recurse
    mod.mkOTarget (Target.active cTarget) |>.activate
  ) |>.insert
  -- Build shared library for `--load-dynlb`
  &`lean.dynlib (mkFacetBuild <| fun mod recurse => do
    let oTarget ← buildFacet mod &`lean.o recurse
    let dynlibTargets ← if mod.shouldPrecompile then
      let (_, transImports) ← buildFacet mod &`lean.imports recurse
      transImports.mapM fun mod => buildFacet mod &`lean.dynlib recurse
    else
      pure #[]
    -- TODO: Link in external libraries
    -- let externLibTargets ← mod.pkg.externLibTargets.mapM (·.activate)
    -- let linkTargets := #[oTarget] ++ sharedLibTargets ++ externLibTargets |>.map Target.active
    let linkTargets := #[oTarget] ++ dynlibTargets |>.map Target.active
    mod.mkDynlibTarget linkTargets |>.activate
  )

/-- Recursively builder for module facets. -/
@[inline] def recBuildModuleFacet : DRecBuild ModuleBuildInfo ModuleBuildData m :=
  have : MonadLift BuildM m := ⟨liftM⟩
  fun info recurse => do
    if let some build := facetBuildMap.find? info.facet then
      build info recurse
    else
      error s!"do not know how to build module facet `{info.facet}`"

/-- Auxiliary function for `buildModuleTop` and `buildModuleTop'`. -/
@[specialize] def buildModuleTopCore (mod : Module)
(facet : WfName) : CycleT ModuleBuildKey m (FacetData facet) :=
  let of_data := by
    simp [ModuleBuildKeyData, ModuleBuildInfo.buildKey, Module.mkBuildKey]
  cast of_data <| buildDTop (m := m) ModuleBuildKeyData (·.buildKey)
    recBuildModuleFacet (ModuleBuildInfo.mk mod facet)

/--
Build the module's specified facet recursively using a topological-sort
based scheduler, storing the results in the monad's store and returning the
result of the top-level build.
-/
@[inline] def buildModuleTop (mod : Module) (facet : WfName)
[h : DynamicType FacetData facet α] : CycleT ModuleBuildKey m α  :=
  let of_data := by rw [h.eq_dynamic_type]
  cast of_data <| buildModuleTopCore mod facet

/--
Build the module's specified facet recursively using a topological-sort
based scheduler, storing the results in the monad's store and returning nothing.
-/
@[inline] def buildModuleTop' (mod : Module) (facet : WfName) : CycleT ModuleBuildKey m PUnit  :=
  discard <| buildModuleTopCore mod facet

end

-- ## Module Map

abbrev ModuleFacetMap :=
  DRBMap ModuleBuildKey ModuleBuildKeyData ModuleBuildKey.quickCmp

def ModuleFacetMap.empty : ModuleFacetMap := DRBMap.empty

-- ## Multi-Module Builders

/--
Recursively build the specified facet of the given module,
returning the result.
-/
def buildModule (mod : Module) (facet : WfName) [DynamicType FacetData facet α] : BuildM α := do
  failOnBuildCycle <| ← EStateT.run' ModuleFacetMap.empty do
    buildModuleTop mod facet

/--
Recursively build the specified facet of each module,
returning an `Array`  of the results.
-/
def buildModuleArray
(mods : Array Module) (facet : WfName)
[DynamicType FacetData facet α] : BuildM (Array α) := do
  failOnBuildCycle <|  ← EStateT.run' ModuleFacetMap.empty <| mods.mapM fun mod =>
    buildModuleTop mod facet

/--
Recursively build the specified facet of the given module,
returning the resulting map of built modules and their results.
-/
def buildModuleMap
(mods : Array Module) (facet : WfName)
[DynamicType FacetData facet α] : BuildM (NameMap α) := do
  let (x, fullMap) ← EStateT.run ModuleFacetMap.empty <| mods.forM fun mod =>
    buildModuleTop' mod facet
  failOnBuildCycle x
  let mut res : NameMap α := RBMap.empty
  for ⟨k, v⟩ in fullMap do
    if h : k.facet = facet then
      let of_data := by
        unfold ModuleBuildKeyData
        simp [h, eq_dynamic_type]
      res := res.insert k.module <| cast of_data v
  return res
