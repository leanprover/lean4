/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Package

open Lean

namespace Lake

/--
A user-configured target -- its package and its configuration.
This is the general structure from which `LeanLib`, `LeanExe`, etc. are derived.
-/
structure ConfigTarget (kind : Name) where
  /-- The package the target belongs to. -/
  pkg : Package
  /-- The target's name. -/
  name : Name
  /-- The target's user-defined configuration. -/
  config : ConfigType kind pkg.name name

instance : Hashable (ConfigTarget k) := ⟨(hash ·.name)⟩
instance : BEq (ConfigTarget k) := ⟨(·.name == ·.name)⟩

@[simp] axiom OpaqueConfigTarget.def {k : Name} : OpaqueConfigTarget k = ConfigTarget k

@[inline] def PConfigDecl.mkConfigTarget (pkg : Package) (self : PConfigDecl pkg.name) : ConfigTarget self.kind :=
  ConfigTarget.mk pkg self.name self.config'

/-- Returns the package targets of the specified kind (as an `Array`). -/
@[inline] def Package.configTargets (kind : Name) (self : Package) : Array (ConfigTarget kind) :=
  self.targetDecls.foldl (init := #[]) fun a t =>
    let {name, kind := k, config, pkg_eq, ..} := t
    if kind_eq : k = kind then
      a.push ⟨self, name, kind_eq ▸ pkg_eq ▸ config⟩
    else
      a

/-- Try to find a package target of the given name and kind. -/
@[inline] def Package.findConfigTarget? (kind : Name) (name : Name) (self : Package) : Option (ConfigTarget kind) :=
  self.findTargetDecl? name |>.bind fun t =>
    let {name, kind := k, config, pkg_eq, ..} := t
    if kind_eq : k = kind then
      some ⟨self, name, kind_eq ▸ pkg_eq ▸ config⟩
    else
      none
