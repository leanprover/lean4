/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Package

namespace Lake
open Lean (Name)

/-- An external library -- its package plus its configuration. -/
structure ExternLib where
  /-- The package the library belongs to. -/
  pkg : Package
  /-- The external library's name. -/
  name : Name
  /-- The library's user-defined configuration. -/
  config : ExternLibConfig pkg.name name

/-- The external libraries of the package (as an Array). -/
@[inline] def Package.externLibs (self : Package) : Array ExternLib :=
  self.externLibConfigs.fold (fun a _ v => a.push ⟨self, _, v⟩) #[]

/-- Try to find a external library in the package with the given name. -/
@[inline] def Package.findExternLib? (name : Name) (self : Package) : Option ExternLib :=
  self.externLibConfigs.find? name |>.map (⟨self, name, ·⟩)

namespace ExternLib

/--
The arguments to pass to `leanc` when linking the external library.
That is, the package's `moreLinkArgs`.
-/
@[inline] def linkArgs (self : ExternLib) : Array String :=
  self.pkg.moreLinkArgs

/-- The name of the package target used to build the external library's static binary. -/
@[inline] def staticTargetName (self : ExternLib) : Name :=
  .str self.name "static"
