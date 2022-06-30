/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.LeanExe
import Lake.Config.ExternLib
import Lake.Build.Facets
import Lake.Util.EquipT

/-!
# Build Info

This module defines the Lake build info type and related utilities.
Build info is what is the data passed to a Lake build function to facilitate
the build.
-/

namespace Lake

/-- The type of Lake's build info. -/
inductive BuildInfo
| module (module : Module) (facet : WfName)
| package (package : Package) (facet : WfName)
| staticLeanLib (lib : LeanLib)
| sharedLeanLib (lib : LeanLib)
| leanExe (exe : LeanExe)
| staticExternLib (lib : ExternLib)
| sharedExternLib (lib : ExternLib)
| custom (package : Package) (target : WfName) (facet : WfName)

--------------------------------------------------------------------------------
/-! ## Build Info & Keys                                                      -/
--------------------------------------------------------------------------------

/-! ### Build Key Helper Constructors -/

abbrev Module.mkBuildKey (facet : WfName) (self : Module) : ModuleBuildKey facet :=
  ⟨⟨none, self.keyName, facet⟩, rfl, rfl⟩

abbrev Package.mkBuildKey (facet : WfName) (self : Package) : PackageBuildKey facet :=
  ⟨⟨self.name, none, facet⟩, rfl, rfl⟩

abbrev LeanLib.staticBuildKey (self : LeanLib) : BuildKey :=
  ⟨self.pkg.name, self.name, staticFacet⟩

abbrev LeanLib.sharedBuildKey (self : LeanLib) : BuildKey :=
  ⟨self.pkg.name, self.name, sharedFacet⟩

abbrev LeanExe.buildKey (self : LeanExe) : BuildKey :=
  ⟨self.pkg.name, self.name, facet⟩

abbrev ExternLib.staticBuildKey (self : ExternLib) : BuildKey :=
  ⟨self.pkg.name, self.name, staticFacet⟩

abbrev ExternLib.sharedBuildKey (self : ExternLib) : BuildKey :=
  ⟨self.pkg.name, self.name, sharedFacet⟩

/-! ### Build Info to Key -/

/-- The key that identifies the build in the Lake build store. -/
abbrev BuildInfo.key : (self : BuildInfo) → BuildKey
| module m f => m.mkBuildKey f
| package p f => p.mkBuildKey f
| staticLeanLib l => l.staticBuildKey
| sharedLeanLib l => l.sharedBuildKey
| leanExe x => x.buildKey
| staticExternLib l => l.staticBuildKey
| sharedExternLib l => l.sharedBuildKey
| custom p t f => ⟨p.name, t, f⟩

/-! ### Instances for deducing data types of `BuildInfo` keys -/

instance [DynamicType ModuleData f α]
: DynamicType BuildData (BuildInfo.key (.module m f)) α where
  eq_dynamic_type := by unfold BuildData; simp [eq_dynamic_type]

instance [DynamicType PackageData f α]
: DynamicType BuildData (BuildInfo.key (.package p f)) α where
  eq_dynamic_type := by unfold BuildData; simp [eq_dynamic_type]

instance [DynamicType TargetData LeanLib.staticFacet α]
: DynamicType BuildData (BuildInfo.key (.staticLeanLib l)) α where
  eq_dynamic_type := by unfold BuildData; simp [eq_dynamic_type]

instance [DynamicType TargetData LeanLib.sharedFacet α]
: DynamicType BuildData (BuildInfo.key (.sharedLeanLib l)) α where
  eq_dynamic_type := by unfold BuildData; simp [eq_dynamic_type]

instance [DynamicType TargetData LeanExe.facet α]
: DynamicType BuildData (BuildInfo.key (.leanExe x)) α where
  eq_dynamic_type := by unfold BuildData; simp [eq_dynamic_type]

instance [DynamicType TargetData ExternLib.staticFacet α]
: DynamicType BuildData (BuildInfo.key (.staticExternLib l)) α where
  eq_dynamic_type := by unfold BuildData; simp [eq_dynamic_type]

instance [DynamicType TargetData ExternLib.sharedFacet α]
: DynamicType BuildData (BuildInfo.key (.sharedExternLib l)) α where
  eq_dynamic_type := by unfold BuildData; simp [eq_dynamic_type]

--------------------------------------------------------------------------------
/-! ## Recursive Building                                                     -/
--------------------------------------------------------------------------------

/-- A build function for any element of the Lake build index. -/
abbrev IndexBuildFn (m : Type → Type v) :=
  -- `DBuildFn BuildInfo (BuildData ·.key) m` with less imports
  (info : BuildInfo) → m (BuildData info.key)

/-- A transformer to equip a monad with a build function for the Lake index. -/
abbrev IndexT (m : Type → Type v) := EquipT (IndexBuildFn m) m

/-- Build the given info using the Lake build index. -/
@[inline] def BuildInfo.recBuild (self : BuildInfo) [DynamicType BuildData self.key α] : IndexT m α :=
  fun build => cast (by simp [eq_dynamic_type]) <| build self

export BuildInfo (recBuild)

--------------------------------------------------------------------------------
/-! ## Build Info & Facets                                                    -/
--------------------------------------------------------------------------------

/-!
### Complex Builtin Facet Declarations

Additional builtin build data types on top of those defined in `FacetData` .
Defined here because they need to import configurations, whereas the definitions
there need to be imported by configurations.
-/

abbrev Module.importFacet := &`lean.imports

/-- The direct × transitive imports of the Lean module. -/
module_data lean.imports : Array Module × Array Module

/-- The package's complete array of transitive dependencies. -/
package_data deps : Array Package


/-!
### Facet Build Info Helper Constructors

Definitions to easily construct `BuildInfo` values for module, package,
and target facets.
-/

namespace Module

/-- Build info for the module's specified facet. -/
abbrev facet (facet : WfName) (self : Module) : BuildInfo :=
  .module self facet

variable (self : Module)

abbrev imports  := self.facet importFacet
abbrev leanBin  := self.facet binFacet
abbrev olean    := self.facet oleanFacet
abbrev ilean    := self.facet ileanFacet
abbrev c        := self.facet cFacet
abbrev o        := self.facet oFacet
abbrev dynlib   := self.facet dynlibFacet

end Module

/-- Build info for the package's specified facet. -/
abbrev Package.facet (facet : WfName) (self : Package) : BuildInfo :=
  .package self facet

/-- Build info for the package's `extraDepTarget`. -/
abbrev Package.extraDep (self : Package) : BuildInfo :=
  self.facet &`extraDep

/-- Build info of the Lean library's static binary. -/
abbrev LeanLib.static (self : LeanLib) : BuildInfo :=
  .staticLeanLib self

/-- Build info of the Lean library's shared binary. -/
abbrev LeanLib.shared (self : LeanLib) : BuildInfo :=
  .sharedLeanLib self

/-- Build info of the Lean executable. -/
abbrev LeanExe.info (self : LeanExe) : BuildInfo :=
  .leanExe self

/-- Build info of the external library's static binary. -/
abbrev ExternLib.static (self : ExternLib) : BuildInfo :=
  .staticExternLib self

/-- Build info of the external library's shared binary. -/
abbrev ExternLib.shared (self : ExternLib) : BuildInfo :=
  .sharedExternLib self
