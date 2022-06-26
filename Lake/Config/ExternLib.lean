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

/-- Try to find a external library in the package with the given name. -/
@[inline] def Package.findExternLib? (name : Name) (self : Package) : Option ExternLib :=
  self.externLibConfigs.find? name |>.map (⟨self, ·⟩)

namespace ExternLib

/-- The external library's user-defined `target`. -/
@[inline] def target (self : ExternLib) : FileTarget :=
  self.config.target
