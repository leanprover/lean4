/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Package
meta import all Lake.Build.Data

/-!
# Build Info

This module defines the Lake build info type and related utilities.
Build info is what is the data passed to a Lake build function to facilitate
the build.
-/

open System Lean

namespace Lake

/-- The type of Lake's build info. -/
public inductive BuildInfo
| target (package : Package) (target : Name)
| facet (target : BuildKey) (kind : Name) (data : DataType.{0} kind) (facet : Name)

--------------------------------------------------------------------------------
/-! ## Build Info & Keys                                                      -/
--------------------------------------------------------------------------------

/-! ### Build Key Helper Constructors -/

public abbrev Package.key (self : Package) : BuildKey :=
  .package self.keyName

public abbrev Package.targetKey (target : Name) (self : Package) : BuildKey :=
  .packageTarget self.keyName target

/-! ### Build Info to Key -/

/-- The key that identifies the build in the Lake build store. -/
@[reducible, expose] public def BuildInfo.key : (self : BuildInfo) → BuildKey
| target p t => p.targetKey t
| facet (target := t) (facet := f) .. => .facet t f

public instance : ToString BuildInfo := ⟨(toString ·.key)⟩

/-! ### Instances for deducing data types of `BuildInfo` keys -/

public instance (priority := low) {p : NPackage n} : FamilyDef BuildData
  (.customTarget p.toPackage.keyName t) (CustomData n t) := ⟨by simp⟩

public instance {p : NPackage n} [FamilyOut (CustomData n) t α]
: FamilyDef BuildData (BuildInfo.key (.target p.toPackage t)) α where
  fam_eq := by unfold BuildData; simp

public instance {p : NPackage n} [FamilyOut BuildData (.packageTarget n t) α]
: FamilyDef BuildData (BuildInfo.key (.target p.toPackage t)) α where
  fam_eq := by unfold BuildInfo.key Package.targetKey; simp

public instance [FamilyOut FacetOut f α]
: FamilyDef BuildData (BuildInfo.key (.facet t k d f)) α where
  fam_eq := by unfold BuildData; simp
