/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Data
import Lake.Config.LeanExe
import Lake.Config.ExternLib
import Lake.Util.EquipT

namespace Lake

-- # Build Key Helper Constructors

abbrev Module.mkBuildKey (facet : WfName) (self : Module) : ModuleBuildKey facet :=
  ⟨⟨none, self.name, facet⟩, rfl, rfl⟩

abbrev Package.mkBuildKey (facet : WfName) (self : Package) : PackageBuildKey facet :=
  ⟨⟨self.name, none, facet⟩, rfl, rfl⟩

abbrev LeanLib.staticFacet := &`leanLib.static
abbrev LeanLib.sharedFacet := &`leanLib.shared
abbrev LeanExe.facet := &`leanExe
abbrev ExternLib.staticFacet := &`externLib.static
abbrev ExternLib.sharedFacet := &`externLib.shared

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

-- # Build Info

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

abbrev BuildInfo.key : (self : BuildInfo) → BuildKey
| module m f => m.mkBuildKey f
| package p f => p.mkBuildKey f
| staticLeanLib l => l.staticBuildKey
| sharedLeanLib l => l.sharedBuildKey
| leanExe x => x.buildKey
| staticExternLib l => l.staticBuildKey
| sharedExternLib l => l.sharedBuildKey
| custom p t f => ⟨p.name, t, f⟩

-- # Instances for deducing data types of `BuildInfo` keys

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

-- # Recursive Facet Builds

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

-- # Build Info Helper Constructors

namespace Module

/-- Build info for the module's specified facet. -/
abbrev facet (facet : WfName) (self : Module) : BuildInfo :=
  .module self facet

abbrev importFacet   := &`lean.imports
abbrev binFacet      := &`lean.bin
abbrev oleanFacet    := &`olean
abbrev ileanFacet    := &`ilean
abbrev cFacet        := &`lean.c
abbrev oFacet        := &`lean.o
abbrev dynlibFacet   := &`lean.dynlib

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

-- # Data Types of Build Results

-- ## For Module Facets

/-- Lean binary build (`olean`, `ilean` files) -/
module_data lean.bin : ActiveOpaqueTarget

/-- The `olean` file produced by `lean`  -/
module_data olean : ActiveFileTarget

/-- The `ilean` file produced by `lean` -/
module_data ilean : ActiveFileTarget

/-- The C file built from the Lean file via `lean` -/
module_data lean.c : ActiveFileTarget

/-- The object file built from `lean.c` -/
module_data lean.o : ActiveFileTarget

/-- Shared library for `--load-dynlib` -/
module_data lean.dynlib : ActiveFileTarget

/-- The direct × transitive imports of the Lean module. -/
module_data lean.imports : Array Module × Array Module

-- ## For Package Facets

/-- The package's complete array of transitive dependencies. -/
package_data deps : Array Package

/-- The package's `extraDepTarget`. -/
package_data extraDep : ActiveOpaqueTarget

-- ## For Target Types

/-- A Lean library's static binary. -/
target_data leanLib.static : ActiveFileTarget

/-- A Lean library's shared binary. -/
target_data leanLib.shared : ActiveFileTarget

/-- A Lean binary executable. -/
target_data leanExe : ActiveFileTarget

/-- A external library's static binary. -/
target_data externLib.static : ActiveFileTarget

/-- A external library's shared binary. -/
target_data externLib.shared : ActiveFileTarget
