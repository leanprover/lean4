/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Package

namespace Lake

/-- An external library -- its package plus its configuration. -/
structure ExternLib where
  /-- The package the library belongs to. -/
  pkg : Package
   /-- The library's user-defined configuration. -/
  config : ExternLibConfig
  deriving Inhabited

/-- The external libraries of the package (as an Array). -/
@[inline] def Package.externLibs (self : Package) : Array ExternLib :=
  self.externLibConfigs.fold (fun a _ v => a.push (⟨self, v⟩)) #[]

/-- Try to find a external library in the package with the given name. -/
@[inline] def Package.findExternLib? (name : Name) (self : Package) : Option ExternLib :=
  self.externLibConfigs.find? name |>.map (⟨self, ·⟩)

namespace ExternLib

/-- The library's well-formed name. -/
@[inline] def name (self : ExternLib) : Name :=
  self.config.name

/-- The external library's user-defined `build`. -/
@[inline] def build (self : ExternLib) : SchedulerM (BuildJob FilePath) :=
  self.config.build

/--
The arguments to pass to `leanc` when linking the external library.
That is, the package's `moreLinkArgs`.
-/
@[inline] def linkArgs (self : ExternLib) : Array String :=
  self.pkg.moreLinkArgs
